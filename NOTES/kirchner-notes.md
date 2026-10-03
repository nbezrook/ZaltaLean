# Notes on Kirchner's thesis (CLAUDE GENERATED)

*Computer-Verified Foundations of Metaphysics and an Ontology of Natural Numbers
in Isabelle/HOL*, Daniel Kirchner, FU Berlin, submitted December 2021.
Local copy: `refs/kirchner-thesis-2021.pdf` (521 pp. + references).

Read so far: abstract, contents, §1.1–§1.2.3, and `AOT_model.thy` head.
Everything below is from those; page refs are thesis pages.

## Structure worth knowing

| Ch. | p. | Why it matters here |
|---|---|---|
| 2 | 7 | Shallow semantic embeddings. **§2.4 Abstraction Layers** (p. 11) and **§2.7 Reproducing the Syntax of the Target Theory** (p. 18) are the two sections our approach is a response to. |
| 3 | 22 | AOT itself. **§3.6 Avoiding Known Paradoxes** (p. 39) and **§3.7 Extending AOT's Free Logic to Relations** (p. 41) — §3.7 is the change Kirchner's own paradox discovery forced. |
| 4 | 48 | The embedding. §4.1 Model Construction, §4.2 Syntax, §4.3 Extending Isabelle's Outer Syntax, §4.7 Meta Theorems (p. 70), **§4.8 Artifactual Theorems (p. 79)**. |
| 5 | 84 | Natural numbers / Frege's theorem. 22 sections. §5.19 The Predecessor Axiom in Detail, §5.20 Modelling Possible Richness of Objects, §5.21 Prospect of an Enhanced Version. |
| 6 | 116 | **Higher-Order Object Theory.** Only 5 pp. — §6.3 Bounded Models, §6.4 Abstract Objects in Unbounded Models. This is where the open problem lives. |
| A | 123 | The Isabelle theory, printed. A.1 Model (p. 123), A.7 The Deductive System PLM (p. 193), A.12 Natural Numbers (p. 419). |

## The three claims to build on

**1. Shallow vs deep is stated outright (p. 3, §1.2.2).** A deep embedding
"defines the syntax of a target system using an inductive data structure and
evaluates statements semantically by recursively traversing this data structure";
an SSE "provides a syntactic translation from the target logic to the meta-logic
… reusing as much of the infrastructure of the meta-logic as possible." Kirchner
chose SSE to inherit Isabelle's automation. The cost is itemized by him, not by us.

**2. Abstraction layers are a workaround for the missing deep embedding (p. 4).**
"An abstraction layer consists of a derivation of the axioms and deduction rules
of a target system from a given semantics that are then considered as ground truth
while 'forgetting' the underlying semantic structure, i.e. the reasoning system is
prevented from using the semantics for proofs." Explicitly motivated as avoiding
artifactual theorems (§4.8) *while keeping* a flexible semantic backend for
exploring axiomatic variations.

→ Our `Thm` / `Deriv` inductives make the "forgetting" structural. But note the
flip side Kirchner names: he keeps the semantic backend precisely so he can
*explore axiomatic extensions and variations*. A deep embedding makes that harder,
not easier. Don't pretend otherwise — build a `Model`-level `satisfies` predicate
early so the same exploration is still available.

**3. Second-order only (p. 2 fn. 3).** "Our embedding currently only extends to
the second-order fragment of AOT. We briefly discuss the challenges of
representing full higher-order object theory in chapter 6." PLM Ch. 15 is *Typed
Object Theory and Applications* — so the gap is real and acknowledged.

## The paradox episode (p. 4, §1.2.3)

Worth having straight, because it is the strongest existing argument for
independent cross-verification:

- Kirchner found "an oversight in an early version of PLM that allowed for the
  reintroduction of a previously known paradox into the system."
- Multiple quick fixes were available, but "in the aftermath of this result AOT was
  significantly reworked and improved."
- It "triggered an extensive debate about the foundations of AOT which culminated
  in the extension of the free logic of AOT to relations, while previously it was
  restricted to individual terms only."

So the current shape of AOT's free logic — the `↓` on relation terms that
`AOT/Defs.lean` leaves as `sorry` — is itself a product of mechanization. Getting
`denotesR` right is not bookkeeping; it is the part of the theory that a prover
changed.

## Prior computational work on AOT (p. 2, §1.2.1)

Pre-SSE, all first-order Prover9 work by Fitelson & Zalta: verified the theorems on
situations and possible worlds, and **found an error in a theorem about Platonic
Forms that had been left as an exercise.** Related Prover9 work: Oppenheimer &
Zalta on Anselm (showing one of three premises suffices), and Spinoza's *Ethics*.
Kirchner's verdict on the approach (p. 3): fine for "concrete isolated arguments",
but "infeasible to construct a natural representation of an entire expressive
higher-order theory and its full deductive system."

## The model, from `AOT_model.thy`

Transcribed into `AOT/Model.lean`. The Isabelle version:

```
typedecl o                                  -- hyperintensional propositions
typedecl w                                  -- worlds
axiomatization do :: o ⇒ (w ⇒ bool) where surj do
consts w0 :: w
axiomatization where ∃w. w ≠ w0
typedef ω = ωset   (countable, nonempty)    -- ordinary urelements
typedef σ' = σ'set (countable, nonempty)
datatype σ = σ'σ σ' | numberσ nat | infiniteσ
typedecl null                               -- null-urelements for non-denoting terms
datatype υ = ωυ ω | συ σ | nullυ null       -- urelements
typedef urrel = {φ. ∀x w. ¬ valid_in w (φ (nullυ x))}
consts ασ :: urrel set ⇒ σ
```

Three things to carry over deliberately:

- `σ = σ' + ℕ + {∞}` is not decoration. The `ℕ` and `∞` summands are what make
  *extended* relation comprehension and the Frege construction work (cf. §5.20
  "Modelling Possible Richness of Objects"). A naive `σ := Set Urrel` is circular.
- The `urrel` condition — necessarily false at every null urelement — *is* the
  negative free logic, in the model.
- `ασ` is a `consts` with no properties in the simple models, constrained further
  for extended comprehension. Hence `Model extends Frame` in our version: the
  frame is fixed, `alphaSigma` is the dial.

## Imports Isabelle needed

`HOL-Cardinals.Bounded_Set`, `HOL-Cardinals.Cardinals`, `HOL-Library.Countable_Set`.
Lean equivalents: `Mathlib.SetTheory.Cardinal.Basic` and friends. Expect this to be
where the model construction actually gets fought.

## Still to read

§2.4–2.7 (abstraction layers and syntax reproduction — directly relevant),
§3.6–3.7 (paradoxes, free logic for relations — needed for `denotesR`),
§4.7–4.9 (meta theorems, artifactual theorems, discussion — the comparison we
have to be fair about), ch. 6 (higher-order — the open problem).
