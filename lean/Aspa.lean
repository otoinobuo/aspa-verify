/-
  Machine-checked analysis of ASPA-based AS_PATH verification
  (draft-ietf-sidrops-aspa-verification-28 and -29, Sections 5.3-5.6)
  and of the ASRA downstream enhancement (draft-sriram-sidrops-asra-verification-05, Section 4).

  Core Lean 4 only (no Mathlib).

  Hops are indexed 0..n-1 in the origin-to-receiver direction: hop i goes from AS(i+1) to AS(i+2)
  (1-based AS numbering of the draft), so a COMPRESSED_AS_PATH of length N has n = N - 1 hops.
-/

/-! ## Abstract layer -/

/-- Result of the provider authorization function (Section 5.3). -/
inductive Auth | provPlus | notProv | noAtt
  deriving DecidableEq, Repr

/-- True business relationship of a hop, in the direction of route propagation.
    `up`: the next AS is a provider of the sender; `down`: a customer; `peer`: a lateral peer. -/
inductive Ty | up | down | peer
  deriving DecidableEq, Repr

/-- One hop: its true type, `authorized(sender, receiver)` and `authorized(receiver, sender)`. -/
structure Hop where
  ty : Ty
  aU : Auth
  aD : Auth
  deriving DecidableEq, Repr

/-- What correct ASPAs guarantee about a hop. -/
def Hop.Correct (h : Hop) : Prop :=
  (h.ty = .up → h.aU ≠ .notProv) ∧ (h.aU = .provPlus → h.ty = .up) ∧
  (h.ty = .down → h.aD ≠ .notProv) ∧ (h.aD = .provPlus → h.ty = .down)

/-- Number of leading elements satisfying `P`. -/
def lead {α} (P : α → Bool) : List α → Nat
  | [] => 0
  | a :: l => if P a then lead P l + 1 else 0

theorem lead_le {α} (P : α → Bool) (l : List α) : lead P l ≤ l.length := by
  induction l with
  | nil => simp [lead]
  | cons a l ih => simp only [lead, List.length_cons]; split <;> omega

theorem lead_spec {α} (P : α → Bool) (l : List α) :
    ∀ i (hi : i < lead P l), P (l[i]'(Nat.lt_of_lt_of_le hi (lead_le P l))) = true := by
  induction l with
  | nil => intro i hi; simp [lead] at hi
  | cons a l ih =>
    intro i hi
    simp only [lead] at hi
    split at hi
    · cases i with
      | zero => simpa
      | succ j => simpa using ih j (by omega)
    · omega

theorem lead_stop {α} (P : α → Bool) (l : List α) (h : lead P l < l.length) :
    P (l[lead P l]'h) = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [lead] at h ⊢
    split
    · rename_i hp
      simp only [hp, ite_true, List.length_cons] at h
      simpa using ih (by omega)
    · rename_i hp; simpa using hp

theorem lead_ge {α} (P : α → Bool) (l : List α) (k : Nat) (hk : k ≤ l.length)
    (h : ∀ i (hi : i < k), P (l[i]'(Nat.lt_of_lt_of_le hi hk)) = true) : k ≤ lead P l := by
  induction l generalizing k with
  | nil => simp at hk; omega
  | cons a l ih =>
    cases k with
    | zero => omega
    | succ k =>
      have ha : P a = true := by simpa using h 0 (by omega)
      have := ih k (by simp at hk; omega) (fun i hi => by simpa using h (i+1) (by omega))
      simp [lead, ha]; omega

theorem lead_congr {α} (P Q : α → Bool) (l : List α) (h : ∀ x ∈ l, P x = Q x) :
    lead P l = lead Q l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [lead, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem lead_stop' {α} (P : α → Bool) (l : List α) (k : Nat) (hk : lead P l = k)
    (h : k < l.length) : P (l[k]'h) = false := by subst hk; exact lead_stop P l h

theorem lead_spec' {α} (P : α → Bool) (l : List α) (k : Nat) (hk : lead P l = k)
    (i : Nat) (hi : i < k) (hl : i < l.length) : P (l[i]'hl) = true := by
  subst hk; exact lead_spec P l i hi

/-- Section 5.4 bounds, as functions of the hop list (`N = hops.length + 1`). -/
def maxUp   (hs : List Hop) : Nat := lead (fun h => h.aU != .notProv) hs + 1
def minUp   (hs : List Hop) : Nat := lead (fun h => h.aU == .provPlus) hs + 1
def maxDown (hs : List Hop) : Nat := lead (fun h => h.aD != .notProv) hs.reverse + 1
def minDown (hs : List Hop) : Nat := lead (fun h => h.aD == .provPlus) hs.reverse + 1

inductive Outcome | valid | invalid | unknown
  deriving DecidableEq, Repr

/-- Section 5.6, steps 4-6 (downstream). -/
def verifyDown (hs : List Hop) : Outcome :=
  let N := hs.length + 1
  if maxUp hs + maxDown hs < N then .invalid
  else if minUp hs + minDown hs < N then .unknown else .valid

/-- Section 5.5, steps 4-6 (upstream: max_down_ramp = min_down_ramp = 0). -/
def verifyUp (hs : List Hop) : Outcome :=
  let N := hs.length + 1
  if maxUp hs < N then .invalid
  else if minUp hs < N then .unknown else .valid

/-- Valley-free (no route leak) for the hops inside the AS_PATH when the route arrives from a
    provider: once a hop is not `up`, every later hop is `down` (up* peer? down*). -/
def ValleyFree (hs : List Hop) : Prop :=
  ∀ i j (hi : i < j) (hj : j < hs.length),
    (hs[i]'(Nat.lt_trans hi hj)).ty ≠ .up → (hs[j]'hj).ty = .down

/-- When the route arrives from a customer, peer or RS, every hop inside the AS_PATH is `up`. -/
def AllUp (hs : List Hop) : Prop := ∀ i (hi : i < hs.length), (hs[i]'hi).ty = .up

def AllCorrect (hs : List Hop) : Prop := ∀ h ∈ hs, h.Correct
/-- Every AS on the path has registered an ASPA. -/
def FullDeployment (hs : List Hop) : Prop := ∀ h ∈ hs, h.aU ≠ .noAtt ∧ h.aD ≠ .noAtt

theorem getElem_rev {α} (l : List α) (i : Nat) (hi : i < l.reverse.length) :
    l.reverse[i] = l[l.length - 1 - i]'(by simp at hi; omega) := by
  simp [List.getElem_reverse]

theorem mem_of_getElem {α} (l : List α) (i : Nat) (hi : i < l.length) : l[i] ∈ l :=
  List.getElem_mem hi

/-! ### Downstream theorems -/

/-- No false positive: a valley-free path is never `Invalid`. -/
theorem down_no_false_positive (hs : List Hop) (hc : AllCorrect hs) (hv : ValleyFree hs) :
    verifyDown hs ≠ .invalid := by
  intro hinv
  obtain ⟨k, hk⟩ : ∃ k, lead (fun h => h.aU != .notProv) hs = k := ⟨_, rfl⟩
  have hkle : k ≤ hs.length := hk ▸ lead_le _ _
  have hlt : maxUp hs + maxDown hs < hs.length + 1 := by
    simp only [verifyDown] at hinv
    split at hinv
    · assumption
    · split at hinv <;> simp at hinv
  by_cases hkn : k = hs.length
  · simp only [maxUp, hk, hkn] at hlt; omega
  · have hklt : k < hs.length := by omega
    have hstop := lead_stop' (fun h => h.aU != .notProv) hs k hk hklt
    have hnotup : (hs[k]'hklt).ty ≠ .up := by
      intro hup
      have := (hc _ (mem_of_getElem hs k hklt)).1 hup
      simp at hstop; exact this hstop
    -- every later hop is down, hence its reverse authorization is not NotProv+
    have hrev : hs.length - 1 - k ≤ lead (fun h => h.aD != .notProv) hs.reverse := by
      apply lead_ge _ _ _ (by simp; omega)
      intro i hi
      rw [getElem_rev]
      have hj : hs.length - 1 - i < hs.length := by omega
      have hdown := hv k (hs.length - 1 - i) (by omega) hj hnotup
      have := (hc _ (mem_of_getElem hs _ hj)).2.2.1 hdown
      simpa using this
    simp only [maxUp, maxDown, hk] at hlt; omega

/-- `Valid` is sound: a `Valid` outcome implies the path is valley-free. -/
theorem down_valid_sound (hs : List Hop) (hc : AllCorrect hs) (hval : verifyDown hs = .valid) :
    ValleyFree hs := by
  simp only [verifyDown] at hval
  split at hval; · simp at hval
  split at hval; · simp at hval
  rename_i _ hge
  intro i j hij hj hi
  let k1 := lead (fun h => h.aU == .provPlus) hs
  let k2 := lead (fun h => h.aD == .provPlus) hs.reverse
  have hsum : hs.length ≤ k1 + k2 + 1 := by simp only [minUp, minDown] at hge; omega
  -- hop i is not up, so i ≥ k1
  have hik : k1 ≤ i := by
    apply Nat.le_of_not_lt; intro hlt
    have hp := lead_spec (fun h => h.aU == .provPlus) hs i hlt
    have := (hc _ (mem_of_getElem hs i (Nat.lt_trans hij hj))).2.1 (by simpa using hp)
    exact hi this
  -- hop j lies in the attested down-ramp
  have hk2 : hs.length - 1 - j < k2 := by omega
  have hp := lead_spec (fun h => h.aD == .provPlus) hs.reverse (hs.length - 1 - j) hk2
  rw [getElem_rev] at hp
  have he : hs.length - 1 - (hs.length - 1 - j) = j := by omega
  simp only [he] at hp
  exact (hc _ (mem_of_getElem hs j hj)).2.2.2 (by simpa using hp)

/-- Completeness under full deployment: the outcome is never `Unknown`. -/
theorem down_full_no_unknown (hs : List Hop) (hf : FullDeployment hs) :
    verifyDown hs ≠ .unknown := by
  have e1 : lead (fun h => h.aU != .notProv) hs = lead (fun h => h.aU == .provPlus) hs := by
    apply lead_congr; intro h hh; have := hf h hh; obtain ⟨t, u, d⟩ := h; cases u <;> simp_all
  have e2 : lead (fun h => h.aD != .notProv) hs.reverse
          = lead (fun h => h.aD == .provPlus) hs.reverse := by
    apply lead_congr; intro h hh; have := hf h (by simpa using hh); obtain ⟨t, u, d⟩ := h; cases d <;> simp_all
  intro hu
  simp only [verifyDown, maxUp, minUp, maxDown, minDown, e1, e2] at hu
  by_cases c : lead (fun h => h.aU == Auth.provPlus) hs + 1
      + (lead (fun h => h.aD == Auth.provPlus) hs.reverse + 1) < hs.length + 1
  · simp [c] at hu
  · simp [c] at hu

/-- Under full deployment, `Valid` iff valley-free, and `Invalid` iff not. -/
theorem down_full_exact (hs : List Hop) (hc : AllCorrect hs) (hf : FullDeployment hs) :
    (verifyDown hs = .valid ↔ ValleyFree hs) ∧ (verifyDown hs = .invalid ↔ ¬ ValleyFree hs) := by
  have h1 := down_no_false_positive hs hc
  have h2 := down_valid_sound hs hc
  have h3 := down_full_no_unknown hs hf
  cases h : verifyDown hs <;> simp_all

/-! ### Upstream theorems -/

theorem up_no_false_positive (hs : List Hop) (hc : AllCorrect hs) (hv : AllUp hs) :
    verifyUp hs ≠ .invalid := by
  have : hs.length ≤ lead (fun h => h.aU != .notProv) hs := by
    apply lead_ge _ _ _ (Nat.le_refl _)
    intro i hi
    have := (hc _ (mem_of_getElem hs i hi)).1 (hv i hi)
    simpa using this
  intro hinv
  simp only [verifyUp, maxUp] at hinv
  by_cases c : lead (fun h => h.aU != Auth.notProv) hs + 1 < hs.length + 1
  · omega
  · by_cases c2 : minUp hs < hs.length + 1 <;> simp [c, c2] at hinv

theorem up_valid_sound (hs : List Hop) (hc : AllCorrect hs) (hval : verifyUp hs = .valid) :
    AllUp hs := by
  simp only [verifyUp] at hval
  split at hval; · simp at hval
  split at hval; · simp at hval
  rename_i _ hge
  intro i hi
  have hk : i < lead (fun h => h.aU == .provPlus) hs := by simp [minUp] at hge; omega
  have hp := lead_spec (fun h => h.aU == .provPlus) hs i hk
  exact (hc _ (mem_of_getElem hs i hi)).2.1 (by simpa using hp)

theorem up_full_no_unknown (hs : List Hop) (hf : FullDeployment hs) :
    verifyUp hs ≠ .unknown := by
  have e1 : lead (fun h => h.aU != .notProv) hs = lead (fun h => h.aU == .provPlus) hs := by
    apply lead_congr; intro h hh; have := hf h hh; obtain ⟨t, u, d⟩ := h; cases u <;> simp_all
  intro hu
  simp only [verifyUp, maxUp, minUp, e1] at hu
  by_cases c : lead (fun h => h.aU == Auth.provPlus) hs + 1 < hs.length + 1
  · simp [c] at hu
  · simp [c] at hu

/-- Appendix B, Property 1 (route-leak detection under partial deployment): if some AS A on the path
    has a (correct) ASPA and the hop out of A is not `up` (A sent the route to a customer or lateral peer),
    then a route received on a customer / lateral-peer / RS interface is `Invalid`. -/
theorem up_property1 (hs : List Hop) (hc : AllCorrect hs) (i : Nat) (hi : i < hs.length)
    (hnotup : (hs[i]'hi).ty ≠ .up) (hatt : (hs[i]'hi).aU ≠ .noAtt) : verifyUp hs = .invalid := by
  have hnp : (hs[i]'hi).aU = .notProv := by
    have hc' := hc _ (mem_of_getElem hs i hi)
    cases h : (hs[i]'hi).aU with
    | provPlus => exact absurd (hc'.2.1 h) hnotup
    | notProv => rfl
    | noAtt => exact absurd h hatt
  have hk : lead (fun h => h.aU != .notProv) hs ≤ i := by
    apply Nat.le_of_not_lt; intro hlt
    have := lead_spec (fun h => h.aU != .notProv) hs i hlt
    simp [hnp] at this
  simp only [verifyUp, maxUp]
  have : lead (fun h => h.aU != .notProv) hs + 1 < hs.length + 1 := by omega
  simp [this]

/-! ## ASRA (draft-sriram-sidrops-asra-verification-05), Step 4 of the downstream enhancement -/

/-- `lat i`: AS(i) has ASPA and ASRA asserting that AS(i+1) is a lateral peer (hop i, 0-based).
    With correct registrations this implies the hop is truly a peer hop. -/
def LatCorrect (hs : List Hop) (lat : Nat → Bool) : Prop :=
  ∀ i (hi : i < hs.length), lat i = true → (hs[i]'hi).ty = .peer

/-- Step 4 as written, Algorithm B range (1-based i from min_up_ramp+1 to N-1, i.e. 0-based hop i-1).
    Algorithm A uses the sub-range ending at N - min_down_ramp, so firing in A implies firing here.
    Steps 2-3 are not modelled; for the counterexample they are checked by hand and in the Python model. -/
def step4Fires (hs : List Hop) (lat : Nat → Bool) : Bool :=
  (List.range hs.length).any (fun i => decide (minUp hs ≤ i) && lat i)

/-- Proposed fix: start from max_up_ramp+1 instead of min_up_ramp+1 (Algorithm B range; A is a sub-range). -/
def step4FixedFires (hs : List Hop) (lat : Nat → Bool) : Bool :=
  (List.range hs.length).any (fun i => decide (maxUp hs ≤ i) && lat i)

/-- The fixed Step 4 is sound: if it fires, the path is not valley-free (it is a route leak). -/
theorem step4_fixed_sound (hs : List Hop) (lat : Nat → Bool) (hc : AllCorrect hs)
    (hl : LatCorrect hs lat) (hf : step4FixedFires hs lat = true) : ¬ ValleyFree hs := by
  intro hv
  simp only [step4FixedFires, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hf
  obtain ⟨i, hi, hmax, hlat⟩ := hf
  have hpeer := hl i hi hlat
  obtain ⟨k, hk⟩ : ∃ k, lead (fun h => h.aU != .notProv) hs = k := ⟨_, rfl⟩
  have hki : k < i := by simp only [maxUp, hk] at hmax; omega
  have hklt : k < hs.length := by omega
  have hstop := lead_stop' (fun h => h.aU != .notProv) hs k hk hklt
  have hnotup : (hs[k]'hklt).ty ≠ .up := by
    intro hup
    have := (hc _ (mem_of_getElem hs k hklt)).1 hup
    simp at hstop; exact this hstop
  have := hv k i hki hi hnotup
  rw [hpeer] at this; exact Ty.noConfusion this

/-- Counterexample to Step 4 as written: path [AS0, AS3, AS2] received by AS1 (a customer of AS2).
    Hop 0: AS0 -> AS3 is `up` (AS3 is AS0's provider); AS0 has no ASPA, AS3 has an ASPA.
    Hop 1: AS3 -> AS2 is `peer`; AS3 has ASPA and ASRA listing AS2 as lateral peer; AS2 has no ASPA. -/
def cexHops : List Hop :=
  [ ⟨.up,   .noAtt,   .notProv⟩,
    ⟨.peer, .notProv, .noAtt⟩ ]
def cexLat : Nat → Bool := fun i => i == 1

theorem cex_correct : AllCorrect cexHops := by
  intro h hh; simp [cexHops] at hh; rcases hh with rfl | rfl <;> simp [Hop.Correct]
theorem cex_lat_correct : LatCorrect cexHops cexLat := by
  intro i hi hl; simp [cexLat] at hl; subst hl; rfl
theorem cex_valley_free : ValleyFree cexHops := by
  intro i j hij hj hi; simp [cexHops] at hj
  have : i = 0 := by omega
  subst this; have : j = 1 := by omega
  subst this; simp [cexHops] at hi
theorem cex_aspa_unknown : verifyDown cexHops = .unknown := by decide
theorem cex_step4_fires : step4Fires cexHops cexLat = true := by decide
theorem cex_fixed_quiet : step4FixedFires cexHops cexLat = false := by decide

#print axioms down_no_false_positive
#print axioms down_valid_sound
#print axioms down_full_no_unknown
#print axioms down_full_exact
#print axioms up_no_false_positive
#print axioms up_valid_sound
#print axioms up_full_no_unknown
#print axioms up_property1
#print axioms step4_fixed_sound
#print axioms cex_step4_fires

/-! ## Concrete layer: AS relationships, ASPA records, and the full hop sequence -/

/-- `rel x y`: the role of AS `y` as seen from AS `x` (`prov`: y is x's provider). -/
inductive Rel | prov | cust | peer
  deriving DecidableEq, Repr

structure Topo where
  rel : Nat → Nat → Option Rel

/-- Relationships are seen consistently from both ends. -/
def Topo.Consistent (T : Topo) : Prop :=
  ∀ x y, (T.rel x y = some .prov ↔ T.rel y x = some .cust)

/-- Section 5.3: provider authorization function over the U-SPAS table. -/
def authorized (spas : Nat → Option (List Nat)) (x y : Nat) : Auth :=
  match spas x with
  | none => .noAtt
  | some s => if y ∈ s then .provPlus else .notProv

/-- Every registered ASPA lists exactly the providers of its customer AS (Section 4). -/
def AspaCorrect (T : Topo) (spas : Nat → Option (List Nat)) : Prop :=
  ∀ x s, spas x = some s → ∀ y, (y ∈ s ↔ T.rel x y = some .prov)

def tyOf (T : Topo) (x y : Nat) : Ty :=
  match T.rel x y with
  | some .prov => .up
  | some .cust => .down
  | _ => .peer

def hopOf (T : Topo) (spas : Nat → Option (List Nat)) (x y : Nat) : Hop :=
  ⟨tyOf T x y, authorized spas x y, authorized spas y x⟩

/-- Hops of an AS path given origin-first. -/
def hopsOf (T : Topo) (spas : Nat → Option (List Nat)) : List Nat → List Hop
  | x :: y :: t => hopOf T spas x y :: hopsOf T spas (y :: t)
  | _ => []

theorem hop_correct (T : Topo) (spas : Nat → Option (List Nat)) (hT : T.Consistent)
    (hA : AspaCorrect T spas) (x y : Nat) : (hopOf T spas x y).Correct := by
  have key : ∀ a b, T.rel a b = some .prov → authorized spas a b ≠ .notProv := by
    intro a b h
    unfold authorized
    cases hs : spas a with
    | none => simp
    | some s => have := (hA a s hs b).2 h; simp [this]
  have key2 : ∀ a b, authorized spas a b = .provPlus → T.rel a b = some .prov := by
    intro a b h
    unfold authorized at h
    cases hs : spas a with
    | none => simp [hs] at h
    | some s =>
      simp only [hs] at h
      split at h
      · rename_i hm; exact (hA a s hs b).1 hm
      · simp at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hup
    simp only [hopOf, tyOf] at hup ⊢
    split at hup
    · rename_i hr; exact key x y hr
    all_goals simp at hup
  · intro hp
    simp only [hopOf, tyOf] at hp ⊢
    rw [key2 x y hp]
  · intro hd
    simp only [hopOf, tyOf] at hd ⊢
    split at hd
    · simp at hd
    · rename_i hr; exact key y x ((hT y x).2 hr)
    · simp at hd
  · intro hp
    simp only [hopOf, tyOf] at hp ⊢
    rw [(hT y x).1 (key2 y x hp)]

theorem hopsOf_correct (T : Topo) (spas : Nat → Option (List Nat)) (hT : T.Consistent)
    (hA : AspaCorrect T spas) (p : List Nat) : AllCorrect (hopsOf T spas p) := by
  induction p with
  | nil => intro h hh; simp [hopsOf] at hh
  | cons x t ih =>
    cases t with
    | nil => intro h hh; simp [hopsOf] at hh
    | cons y t =>
      intro h hh
      simp only [hopsOf, List.mem_cons] at hh
      rcases hh with rfl | hh
      · exact hop_correct T spas hT hA x y
      · exact ih h hh

/-! ### Ground truth on the full hop sequence (including the hop into the receiver) -/

/-- Valley-free condition on any hop-type list: once a hop is not `up`, every later hop is `down`. -/
def VF (ts : List Ty) : Prop :=
  ∀ i j (hi : i < j) (hj : j < ts.length), ts[i]'(Nat.lt_trans hi hj) ≠ .up → ts[j]'hj = .down

theorem vf_snoc_down (ts : List Ty) : VF (ts ++ [.down]) ↔ VF ts := by
  constructor
  · intro h i j hi hj hne
    have := h i j hi (by simp; omega) (by rwa [List.getElem_append_left (by omega)])
    rwa [List.getElem_append_left hj] at this
  · intro h i j hi hj hne
    simp at hj
    by_cases hjl : j < ts.length
    · rw [List.getElem_append_left hjl]
      exact h i j hi hjl (by rwa [List.getElem_append_left (by omega)] at hne)
    · have : j = ts.length := by omega
      subst this; simp

theorem vf_snoc_nondown (ts : List Ty) (t : Ty) (ht : t ≠ .down) :
    VF (ts ++ [t]) ↔ ∀ i (hi : i < ts.length), ts[i] = .up := by
  constructor
  · intro h i hi
    apply Decidable.byContradiction; intro hne
    have := h i ts.length hi (by simp) (by rwa [List.getElem_append_left hi])
    simp at this; exact ht this
  · intro h i j hij hj hne
    have hlen : (ts ++ [t]).length = ts.length + 1 := by simp
    have hit : i < ts.length := by omega
    exfalso; apply hne
    rw [List.getElem_append_left hit]
    exact h i hit

theorem valleyFree_iff (hs : List Hop) : ValleyFree hs ↔ VF (hs.map (·.ty)) := by
  constructor
  · intro h i j hi hj hne; simp at hj ⊢; exact h i j hi hj (by simpa using hne)
  · intro h i j hi hj hne; have := h i j hi (by simpa using hj) (by simpa using hne); simpa using this

theorem allUp_iff (hs : List Hop) : AllUp hs ↔ ∀ i (hi : i < (hs.map (·.ty)).length), (hs.map (·.ty))[i] = .up := by
  constructor
  · intro h i hi; simp at hi ⊢; exact h i hi
  · intro h i hi; have := h i (by simpa using hi); simpa using this

/-! ### Main results at the concrete level -/

/-- Downstream (route received from a provider: the last hop into the receiver is `down`). -/
theorem aspa_downstream (T : Topo) (spas : Nat → Option (List Nat)) (hT : T.Consistent)
    (hA : AspaCorrect T spas) (p : List Nat) :
    let hs := hopsOf T spas p
    let leakFree := VF (hs.map (·.ty) ++ [.down])
    (leakFree → verifyDown hs ≠ .invalid) ∧ (verifyDown hs = .valid → leakFree) := by
  intro hs leakFree
  have hc := hopsOf_correct T spas hT hA p
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact down_no_false_positive hs hc ((valleyFree_iff hs).2 ((vf_snoc_down _).1 h))
  · exact (vf_snoc_down _).2 ((valleyFree_iff hs).1 (down_valid_sound hs hc h))

/-- Upstream (route received from a customer, a lateral peer, or an RS: the last hop is not `down`). -/
theorem aspa_upstream (T : Topo) (spas : Nat → Option (List Nat)) (hT : T.Consistent)
    (hA : AspaCorrect T spas) (p : List Nat) (last : Ty) (hl : last ≠ .down) :
    let hs := hopsOf T spas p
    let leakFree := VF (hs.map (·.ty) ++ [last])
    (leakFree → verifyUp hs ≠ .invalid) ∧ (verifyUp hs = .valid → leakFree) := by
  intro hs leakFree
  have hc := hopsOf_correct T spas hT hA p
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact up_no_false_positive hs hc ((allUp_iff hs).2 ((vf_snoc_nondown _ last hl).1 h))
  · exact (vf_snoc_nondown _ last hl).2 ((allUp_iff hs).1 (up_valid_sound hs hc h))

#print axioms hop_correct
#print axioms aspa_downstream
#print axioms aspa_upstream

/-! ## Worked examples of [aspa-examples] (Sriram, Borchert, Matejka; Oct 2026), Tables 1-3.
    Each row checks the four bounds and the outcome by kernel evaluation (`decide`).
    The hop types are irrelevant to the procedure and are set to `peer`. -/
/-- T1 #1: G receives F C A (upstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = 3 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = 3 ∧ verifyUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = .valid := by decide
/-- T1 #2: G receives D C A (upstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩] = 2 ∧ verifyUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩] = .invalid := by decide
/-- T1 #3: G receives D F C A (upstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = 4 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = 3 ∧ verifyUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = .unknown := by decide
/-- T1 #4: C receives D E B (upstream). -/
example : maxUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = 3 ∧ minUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = 2 ∧ verifyUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = .unknown := by decide
/-- T1 #5: C receives A D E B (upstream). -/
example : maxUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 3 ∧ minUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ verifyUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = .invalid := by decide
/-- T1 #6: C receives A D G E B (upstream). -/
example : maxUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = 3 ∧ minUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ verifyUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = .invalid := by decide
/-- T1 #7: D receives A C F (upstream). -/
example : maxUp [⟨.peer, .noAtt, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ minUp [⟨.peer, .noAtt, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = 1 ∧ verifyUp [⟨.peer, .noAtt, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = .invalid := by decide
/-- T1 #8: D receives A C F G (upstream). -/
example : maxUp [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = 1 ∧ minUp [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = 1 ∧ verifyUp [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩, ⟨.peer, .notProv, .provPlus⟩] = .invalid := by decide
/-- T1 #9: D receives E B (upstream). -/
example : maxUp [⟨.peer, .provPlus, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .noAtt⟩] = 2 ∧ verifyUp [⟨.peer, .provPlus, .noAtt⟩] = .valid := by decide
/-- T2 #1: B receives E G F C A (downstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 4 ∧ maxDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 3 ∧ minDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = .unknown := by decide
/-- T2 #2: B receives E G D A (downstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 3 ∧ maxDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 3 ∧ minDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = .valid := by decide
/-- T2 #3: B receives E D C A (downstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ maxDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = .unknown := by decide
/-- T2 #4: B receives E G D C A (downstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ maxDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .notProv⟩, ⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = .invalid := by decide
/-- T2 #5: A receives C F D G (downstream). -/
example : maxUp [⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = 1 ∧ maxDown [⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = 4 ∧ minUp [⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = 1 ∧ minDown [⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = 2 ∧ verifyDown [⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .provPlus⟩] = .unknown := by decide
/-- T2 #6: A receives D G E B (downstream). -/
example : maxUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 3 ∧ maxDown [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ minDown [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ verifyDown [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = .valid := by decide
/-- T2 #7: A receives C D G E B (downstream). -/
example : maxUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .notProv⟩] = 3 ∧ maxDown [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .notProv⟩] = 1 ∧ minUp [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .notProv⟩] = 2 ∧ minDown [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .notProv⟩] = 1 ∧ verifyDown [⟨.peer, .provPlus, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩, ⟨.peer, .notProv, .notProv⟩] = .invalid := by decide
/-- T2 #8: D receives F C A (downstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = 3 ∧ maxDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = 3 ∧ minDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = 1 ∧ verifyDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .provPlus, .noAtt⟩] = .valid := by decide
/-- T2 #9: B receives E A (downstream). -/
example : maxUp [⟨.peer, .notProv, .noAtt⟩] = 1 ∧ maxDown [⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .notProv, .noAtt⟩] = 1 ∧ minDown [⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyDown [⟨.peer, .notProv, .noAtt⟩] = .valid := by decide
/-- T2 #10: B receives E C A (downstream). -/
example : maxUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ maxDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minUp [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 2 ∧ minDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyDown [⟨.peer, .provPlus, .notProv⟩, ⟨.peer, .notProv, .noAtt⟩] = .valid := by decide
/-- T3 #1: K receives J H (upstream). -/
example : maxUp [⟨.peer, .notProv, .noAtt⟩] = 1 ∧ minUp [⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyUp [⟨.peer, .notProv, .noAtt⟩] = .invalid := by decide
/-- T3 #2: K receives J H (upstream). -/
example : maxUp [⟨.peer, .notProv, .noAtt⟩] = 1 ∧ minUp [⟨.peer, .notProv, .noAtt⟩] = 1 ∧ verifyUp [⟨.peer, .notProv, .noAtt⟩] = .invalid := by decide
/-- T3 #3: L receives K J H (downstream). -/
example : maxUp [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = 1 ∧ maxDown [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = 1 ∧ minUp [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = 1 ∧ minDown [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = 1 ∧ verifyDown [⟨.peer, .notProv, .noAtt⟩, ⟨.peer, .noAtt, .notProv⟩] = .invalid := by decide
/-- T3 #4: R receives Q P (upstream). -/
example : maxUp [⟨.peer, .notProv, .notProv⟩] = 1 ∧ minUp [⟨.peer, .notProv, .notProv⟩] = 1 ∧ verifyUp [⟨.peer, .notProv, .notProv⟩] = .invalid := by decide
/-- T3 #5: R receives Q P (downstream). -/
example : maxUp [⟨.peer, .notProv, .notProv⟩] = 1 ∧ maxDown [⟨.peer, .notProv, .notProv⟩] = 1 ∧ minUp [⟨.peer, .notProv, .notProv⟩] = 1 ∧ minDown [⟨.peer, .notProv, .notProv⟩] = 1 ∧ verifyDown [⟨.peer, .notProv, .notProv⟩] = .valid := by decide
/-- T3 #6: S receives R Q P (downstream). -/
example : maxUp [⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 1 ∧ maxDown [⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ minUp [⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 1 ∧ minDown [⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = 2 ∧ verifyDown [⟨.peer, .notProv, .notProv⟩, ⟨.peer, .notProv, .provPlus⟩] = .valid := by decide
