# The kernel and measure representations of Latinons agree — Lean formalization

Juan Pablo Traverso Gianini · Research note, preprint 1.0 · Apache-2.0

[Read the note on alphaXiv](https://www.alphaxiv.org/abs/2611.latinons-kernel-measure-lean-formalization) ·
[Bilingual note, frozen Lean archive and evidence](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/ghhsbridge-v1.0)

The Latinon preprint states and verifies its theorems for Latinons described by measures on
the unit cube, while Conjecture 12.4 of Garbe, Hancock, Hladký and Sharifzadeh is written for
Latinons described by kernels. This repository proves in Lean that the two descriptions agree,
with the same cut distance, pattern densities and entropy, and derives Conjecture 12.4 in the
definitions of Garbe et al. on the ground space [0,1], with entropy taken as minus relative
entropy.

`BridgeChallenge.lean` is the standalone, Mathlib-only statement interface. `BridgeSolution.lean`
re-exports the proved declarations through the aggregate `GHHSBridge`. The Latinon formalization
is a pinned Lake dependency
([`jtraverso/latinon-entropy-ldp-lean@ec7025d`](https://github.com/jtraverso/latinon-entropy-ldp-lean/tree/ec7025d0ecc2292292f3928183e9f03db420f379)).

## Compared claims

| Declaration in `GHHSBridge` | Meaning |
| --- | --- |
| `toLatinonMeasure_ofLatinonMeasure` | Measure ⇒ kernel ⇒ measure is the identity. |
| `ofLatinonMeasure_toLatinonMeasure_kernel` | Kernel ⇒ measure ⇒ kernel returns the kernel almost everywhere. |
| `ghhsCutDistance_eq` | The GHHS cut distance equals the cut distance of the measure representations. |
| `ghhsPatternDensity_eq` | GHHS pattern densities equal those of the measure representation. |
| `klDiv_compProd_right_eq_lintegral` | Conditional chain rule for relative entropy. |
| `ghhsEntropy_eq` | GHHS entropy (sign −KL) equals the entropy of the measure representation. |
| `ghhsEntSup_eq` | The supremum in Conjecture 12.4 is minus the contracted rate. |
| `ghhsConjecture_12_4` | Conjecture 12.4 when the supremum is finite. |
| `ghhsConjecture_12_4_bot`, `ghhsConjecture_12_4_bot'` | Conjecture 12.4 when the supremum is −∞. |

Auxiliary compared statements: the three marginal identities of kernel integration, the row and
column permuton lemmas, the disintegration identity, and five certificates that Lean generates
inside definitions (compared by statement).

The source modules in `GHHSBridge/` are the frozen sources of the note with module-system
adapters only; `evidence/PACKAGING.json` records the source archive hash and each adapter.
