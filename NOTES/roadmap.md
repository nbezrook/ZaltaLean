# Roadmap (CLAUDE GENERATED)

Ordered so that each step can falsify the approach as cheaply as possible. If the
deep embedding is going to fail, it fails at step 2 or step 4 — do those before
writing any more object theory.

## Phase 0 — make it compile — **DONE**

`lake build` is green on all 9 modules; only the intended `sorry` warnings remain.

Worth recording what I predicted would break versus what actually did, because the
prediction was mostly wrong in a useful direction:

| Predicted failure | Outcome |
|---|---|
| `deriving` handlers on the mutual nested inductive | Never arose — the `deriving Repr` lines had already been stripped. Instances are still **absent**; write them when something needs `DecidableEq`. |
| Termination of mutual `encPosF` / `freeIF` over `List Term` | Compiled with no complaint. Keeping the list helpers inside the same `mutual` block was sufficient; no `termination_by` needed. |
| `Frame.Urrel` / `Frame.Obj` double-binding `F` | Not an error. Compiles as written. |
| `Model extends Frame` with `toFrame.Urrel` in a later field | Not an error. `extends` is fine. |

The three fixes actually required were mundane: `List.get?` (gone in 4.35) replaced
by an explicit `isIvarSeq` recursion; `Nat.rec` for iterated `∀` replaced by a named
`alliN`; and `Mathlib.Data.Countable.Defs` renamed to `Mathlib.Basic.Countable.Defs`.

**Conclusion: the deep embedding is not fighting Lean at the syntax level.** The
real risk is entirely in Phase 1 — which is where it always was.

## Phase 1 — the load-bearing obligations

3. **`nonempty_model`** (`AOT/Model.lean`). Until this is proved everything else is
   vacuous. The sketch in the file hits the circularity `Sg ≈ Set Urrel`, which is
   exactly what the Aczel construction solves and why Isabelle uses a countable
   `σ'` plus `ℕ` plus `∞`. Budget real time; reach for `Mathlib.SetTheory.Cardinal`.

4. **`shiftI` / `substI`** (`AOT/Occurrence.lean`) plus the commutation lemmas
   `substI_shiftI`, `freeIF_substI`, `encPosF_substI`. This is the tax a deep
   embedding pays and the SSE does not. If it is miserable, that is the signal to
   reconsider — consider a locally-nameless or well-scoped (`Fin n`-indexed)
   representation before pressing on.

5. **Resolve the encoding-position fork.** `AOT/Occurrence.lean` flags it: does a
   variable inside a description inside an encoding slot count? Read PLM Ch. 7.1
   (Metatheoretical Definitions) and decide with a citation. Getting this wrong in
   one direction readmits Clark/Boolos; in the other it weakens the system.

## Phase 2 — close the axiom set

6. Transcribe PLM 8.1–8.6 (items 38.x, 39.x, substitution of identicals, actuality,
   necessity, necessity+actuality). `AOT/Axioms.lean` lists exactly what is missing.
   Transcribe from the PDF, not from memory, and record item numbers + the draft date.
7. `denotesR` and `eqRel` (PLM 7.2.2–7.2.3). Per `NOTES/kirchner-notes.md`, the free
   logic *for relations* is itself a product of mechanization — read thesis §3.7 first.
8. `ax_enc_reduction` for `n = 2`, then generalize.

## Phase 3 — the results that justify the project

9. **Soundness**: `Thm f → valid f`. Needs `denoteT/denoteR/denoteF`.
10. **No modal collapse**: `Deriv [f] (box f)` does not hold in general — i.e.
    omitting RN from `Deriv` has content. Soundness + a two-world model. Cheapest
    non-trivial check available; do it the moment soundness lands.
11. **Clark/Boolos**: `clark_boolos_fails` in `AOT/Theorems/Basic.lean`. The term is
    *writable* in our syntax and must be *provably* non-denoting. This is the
    faithfulness test.
12. **PLM theorem 230**: `[λxy O!x & O!y & x =E y]↓` via Coexistence (item 49), not
    β-Conversion. If this works the free-logic layer is right.
13. **Metatheory as theorems**: PLM's Rules of Substitution (item 160) and the
    illegitimate uses in item 161. Nothing in the SSE literature states these as
    object-level theorems. This is the first genuinely new result available.

## Phase 4 — where the contribution is largest

14. **A notation/elaborator layer.** Lean's `syntax`/`macro`/`elab` should do what
    `AOT_syntax.ML` + `AOT_commands.ML` (1,600 lines of Isabelle/ML) do, in far
    less code, with modal strictness tracked in the elaborator. Good standalone
    write-up even on its own.
15. **PLM drift audit.** Kirchner targets the 2021-10-13 draft; current is
    2026-05-15. Diff the axioms and the numbered items. Cheap, immediately useful
    to Zalta/Kirchner, and a sensible way to make first contact.
16. **The chapters Isabelle has not reached.** No `AOT_*.thy` corresponds to PLM
    Ch. 11 (Platonic Forms), Ch. 13 (Concepts), or Ch. 15 (Typed Object Theory);
    Ch. 12 is only partly covered by `AOT_Hype.thy` / `AOT_TruthmakerSemantics.thy`.
    Ch. 15 is the one where dependent types should structurally beat simple types —
    and thesis ch. 6 concedes higher-order object theory is open.
17. **Mathlib bridge.** Interpret AOT's natural numbers (PLM Ch. 14) into
    `Mathlib`'s `Nat`. Nobody has connected a metaphysical foundation of arithmetic
    to a working mathematical library.

## Things to not kid ourselves about

- The SSE inherits `sledgehammer`, `nitpick`, and all of HOL's automation. We
  inherit `simp`, `grind`, and `decide` over our own syntax — which is *worse* for
  proof search over object-level formulas until a tactic layer exists (step 14).
- Kirchner keeps the semantic backend deliberately, to explore axiomatic variants
  (thesis §2.4). A deep embedding makes that harder. Build `satisfies` early so
  model-level exploration stays possible.
- Re-deriving Frege's theorem is ~8,000 lines in `AOT_NaturalNumbers.thy` alone. It
  is not the near-term target; steps 10–13 are.
- First contact with Kirchner/Zalta should probably be step 15, not an announcement.
