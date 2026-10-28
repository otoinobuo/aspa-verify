# aspa-verify

Securing Internet routing: machine-checked proofs for ASPA route-leak detection (BGP / RPKI) and a false-positive flaw in the ASRA extension.

- **ASPA**: draft-ietf-sidrops-aspa-verification-29, Sections 5.3–5.6 (5.4–5.6 identical to -28)
  <https://datatracker.ietf.org/doc/draft-ietf-sidrops-aspa-verification/29/>
- **ASRA**: draft-sriram-sidrops-asra-verification-05
  <https://datatracker.ietf.org/doc/draft-sriram-sidrops-asra-verification/05/>
- **Examples**: Sriram, Borchert, Matejka, "ASPA-based AS path verification examples", Oct 2026
  <https://github.com/ksriram25/IETF/blob/main/ASPA_path_verification_examples.pdf>

Paper: `paper/aspa-verify.pdf` (LaTeX source `paper/aspa-verify.tex`).
Archived version (paper and artifacts): https://doi.org/10.5281/zenodo.23734450

## How to cite

Nobuo Otoi. *Securing Internet Routing: Machine-Checked Proofs for ASPA Route-Leak Detection and a False-Positive Flaw in the ASRA Extension.* Preprint, version 1, October 2026. Zenodo. https://doi.org/10.5281/zenodo.23734450

## Lean (`lean/Aspa.lean`)

Lean 4 v4.33.1, core only, no Mathlib, no lakefile needed:

    cd lean && lean Aspa.lean

It takes a few seconds. A successful run prints only 13 `#print axioms` lines and exits with status 0. None of them
mentions `sorryAx` or `Classical.choice`; `cex_step4_fires` depends on no axioms. The 25 rows of the examples
document are checked with `decide`.

Main theorems:

| Theorem | Statement |
|---|---|
| `down_no_false_positive`, `up_no_false_positive` | A valley-free path is never Invalid |
| `down_valid_sound`, `up_valid_sound` | Valid implies valley-free |
| `up_property1` | Appendix B, Property 1 |
| `down_full_no_unknown`, `up_full_no_unknown`, `down_full_exact` | Under full deployment there is no Unknown, and the outcome is exact |
| `aspa_downstream`, `aspa_upstream` | The same, for a topology and an ASPA table (consistency and ASPA correctness) |
| `step4_fixed_sound` | The modified ASRA Step 4 fires only on route leaks |
| `cex_*` | Counterexample to ASRA Step 4 as written |

## Python (`model/`)

Python 3, standard library only. `model.py` and `asra.py` are literal transcriptions of the procedures; the others
are checkers.

| Command | Expected result | Time |
|---|---|---|
| `python examples.py` | `match 25 mismatch 0` | instant |
| `python check.py 4` | no violations, 626,688 cases | a few min |
| `python check.py 4 rs` | no violations, 835,224 cases | a few min |
| `python check_asra.py 4` | Alg A and Alg B: 4,608 false positives each | a few min |
| `python fixcheck.py 4` | all false positives from step 4; none with the fix; 15,360 vs 6,144 extra detections | a few min |
| `python lost.py` | all 9,216 cases lost by the fix have the shape (lateral hop = first Not Provider+, previous hop No Attestation) | a few min |

## License

Apache-2.0. Author: Nobuo Otoi (BA Cybersecurity).
