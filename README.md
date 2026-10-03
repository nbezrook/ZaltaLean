# ZaltaLean

an attempt at the **deep embedding** of Edward Zalta's Abstract Object Theory (AOT), as presented in
*Principia Logico-Metaphysica* (PLM) in Lean 4.

> **current:** `lake build` succeeds on all 9 modules with
> only the intended `sorry` warnings. *definitions* typecheck. see [current state](#current state).

## details

canonical mechanization of AOT is Daniel Kirchner's, in Isabelle/HOL
([ekpyron/AOT](https://github.com/ekpyron/AOT), [AFP entry](https://isa-afp.org/entries/AOT.html),
[thesis](https://refubium.fu-berlin.de/bitstream/handle/fub188/35426/dissertation_kirchner.pdf)). This project is not an attempt to redo it in another syntax.

Kirchner: **shallow semantic embedding**; object-language
expressions are translated into HOL at parse time. 1.2.2 draws the
contrast explicitly. a deep embedding instead "defines the syntax of a target
system using an inductive data structure and evaluates statements semantically by
recursively traversing this data structure." reasoning: "SSEs are a means for universal logical reasoning by translating a target logic to HOL
using a representation of its semantics."

two questions

1. **Artifactual theorems** (4.8). Because the semantics is always in scope, facts
   true in the model but *not* derivable in AOT are provable. The workaround is
   *abstraction layers* (2.4): derive the axioms and rules from the semantics, then
   deliberately "forget" the semantics so the reasoner can only use the derived
   rules. This is a discipline, enforced by convention and by tooling.

2. **Side conditions live outside the logic.** AOT's restriction on λ-abstraction —
   no abstracting over a variable in *encoding* position, on pain of the
   Clark/Boolos paradox (PLM p. 298 fn. 170) — is enforced by `AOT_syntax.ML` at
   parse time. Likewise modal strictness, enforced by custom `AOT_theorem` /
   `AOT_act_theorem` outer-syntax commands (4.3).

In a deep embedding both become structural. Artifactual theorems are *impossible*:
`Thm` is an inductive predicate that never mentions a model, so soundness
(`Thm f → valid f`) is a theorem to prove rather than a property to be careful
about. And the side conditions become decidable Lean `Prop`s carried by the axiom
schemas themselves, which means PLM's metatheory — the Rules of Substitution
(item 160) and its catalogue of *illegitimate* uses (item 161), the GEN and RN
metarules (9.3), modal strictness (9.2) — becomes checkable rather than conventional.

note: SSE gets substitution, α-equivalence, and all of HOL's automation for free. are deep embeddings possible?

## Layout

| File | Contents |
|---|---|
| `AOT/Syntax.lean` | De Bruijn syntax for the primitives of PLM 8.10: exemplification, encoding, `E!`, `¬ → ∀ □ 𝒜 ι λ`. Deliberately unrestricted. |
| `AOT/Occurrence.lean` | `encPosF` (occurrence in encoding position), `freeIF`, `elementaryMatrix`. The side conditions. Substitution is **unimplemented**. |
| `AOT/Defs.lean` | The *defined* notions: `& ≡ ∃ ◇ O! A! ↓ =`. Kept as `def`s so PLM 9.4/9.13 on the inferential role of definitions stays checkable. |
| `AOT/Model.lean` | Aczel-style frames as a `structure`, not `axiom`s — so "there are models" is a theorem (`nonempty_model`), not a Nitpick check. |
| `AOT/Semantics.lean` | Denotation signatures. All `sorry`. |
| `AOT/Axioms.lean` | PLM Ch. 8 axioms, with provenance and an explicit list of what has **not** been transcribed yet. |
| `AOT/Deduction.lean` | `Thm` (modally strict) and `Deriv` (from premises, no RN). Soundness as a target. |
| `AOT/Theorems/Basic.lean` | Four first targets, chosen to test the free-logic layer. |
| `NOTES/` | Study notes on Kirchner's thesis; roadmap with ordered obligations. |
| `refs/` | Kirchner's thesis + two papers, and a shallow clone of the Isabelle development. Gitignored. |

## Building

```bash
lake build
```

Pinned to **Lean v4.35.0-rc3** and **Mathlib `282fbb8`** — the pairing already
built in the sibling project `Z:\LeanDecisionTheory`, whose packages this project
reuses through a junction at `.lake/packages`. That junction is why there is no
`lake update` step and why nothing had to be downloaded.

Two environment facts worth recording, because they will bite again:

- `elan` lives on `Z:\elan`, not in the default `%USERPROFILE%\.elan`. **`C:` is out
  of disk space**, so `ELAN_HOME=Z:\elan` must be set or elan will try to download
  a toolchain to `C:` and fail with `os error 112`.
- This project must stay on a local NTFS volume. It originally lived on `G:`
  (Google Drive), where junctions are impossible ("Local NTFS volumes are
  required") and where Google Drive rejects olean overwrites with error 87,
  silently leaving stale build artifacts. Do not move it back.

If the junction is ever lost, recreate it with:

```bash
cmd //c mklink /J "Z:\ZaltaLean\.lake\packages" "Z:\LeanDecisionTheory\.lake\packages"
```

## Conventions

- **no silent `sorry`.** An incomplete proof is written `sorry -- TODO: <what
  remains>`, so that grepping for `sorry` finds a description of the gap. No axioms
  are declared — which here is load-bearing rather than stylistic, since the point
  of making `Frame` a `structure` instead of an `axiomatization` is that nothing is
  asserted to Lean's kernel.

- **please make sure you understand your ai-generated code.** Proofs may be drafted
  with AI assistance, but nothing is committed until the person committing it can
  explain every line: what each hypothesis is doing, why each step follows, and what
  would break if a hypothesis were dropped. A proof that compiles and is not
  understood is worse than no proof, because it cannot be maintained, generalised,
  or trusted when Mathlib moves underneath it. Disclose AI assistance in the commit
  message or PR description.

- **Commit messages, issues and review comments are handwritten.** They are the
  record of why a change was made and they are how a reader judges whether the
  author understood the change. This also keeps the repository compliant with
  Mathlib's contribution policy, which requires AI assistance to be disclosed, bars
  LLM-written comments on GitHub and Zulip, and expects the submitter to understand
  every line.

## current state

- 15 `sorry`s, all deliberate and annotated. Everything else typechecks.
- `shiftI` / `substI` are stubs. Nothing involving instantiation can work until they exist.
- `nonempty_model` is the load-bearing obligation: **until it is proved, every
  theorem here is vacuous.** The sketch in `AOT/Model.lean` runs into the
  cardinality problem that the Aczel construction exists to solve, and says so.
- `denotesR` and `eqRel` (PLM 7.2.2–7.2.3) are left as `sorry` rather than guessed,
  because guessing them wrong silently breaks the free logic.
- `AOT/Occurrence.lean`: whether a
  variable occurring inside a description that sits in an encoding slot counts as
  occurring "in encoding position". Resolve against PLM Ch. 7.1

## Version pinning

PLM is a live document. This development targets the draft of **2026-05-15**
(upstream at <https://mally.stanford.edu/principia.pdf>).

## References

- Zalta, *Principia Logico-Metaphysica*, draft 2026-05-15, with contributions by Daniel Kirchner and Uri Nodelman. <https://mally.stanford.edu/principia.pdf>
- Kirchner, *Computer-Verified Foundations of Metaphysics and an Ontology of Natural Numbers in Isabelle/HOL*, PhD thesis, FU Berlin, 2021. <https://doi.org/10.17169/REFUBIUM-35141>
- Kirchner, Benzmüller, Zalta, *Mechanizing Principia Logico-Metaphysica in Functional Type Theory*, RSL 2020. <https://mally.stanford.edu/Papers/mechanizing-principia.pdf>
- Kirchner, *Computer Science and Metaphysics: A Cross-Fertilization*. <https://mally.stanford.edu/Papers/cs-metaphysics.pdf>
