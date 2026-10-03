/-
# deductive system (PLM Ch. 9).

`Thm f`      -- `f` is a theorem by a **modally strict** proof.
`Deriv G f`  -- `f` is derivable from premises `G`, not necessarily strictly.

PLM 9.2 distinguishes modally strict proofs from ordinary ones, and
the distinction has teeth. RN (the Rule of Necessitation, 9.3) may be applied
only inside a modally strict proof; the Rules of Substitution (9.13 item 160)
likewise require either `Box (f == g)` or a *modally strict* proof of `f == g`,
and PLM item 161 catalogues what goes wrong when that is ignored.
-/

import AOT.Axioms
import AOT.Semantics

namespace AOT
open Formula
/-- Modally strict theoremhood. -/
inductive Thm : Formula -> Prop where
  /-- PLM 9.1: Modus Ponens is the sole primitive rule. -/
  | mp {f g} : Thm (imp f g) -> Thm f -> Thm g
  /-- PLM 9.3: RN. Admissible only here, never in `Deriv`. -/
  | rn {f} : Thm f -> Thm (box f)
  /-- PLM 9.3: GEN. -/
  | gen {f} : Thm f -> Thm (alli f)
  | genR {n f} : Thm f -> Thm (allr n f)
  -- Axioms (universal closures; see `AOT/Axioms.lean` for provenance).
  | descriptions {f} : Thm (alliN 1 (ax_descriptions f))
  | beta {n f} (h : forall i, i < n -> encPosF i f = false) :
      Thm (alliN n (ax_beta n f h))
  | eta {n f} (h : elementaryMatrix n f = true) : Thm (ax_eta n f h)
  | coexistence {n f g} : Thm (alliN n (ax_coexistence n f g))
  | encRigid : Thm (alliN 1 ax_enc_rigid)
  | ordNoEnc : Thm (alliN 1 ax_ord_no_enc)
  | comprehension {f} (h : freeIF 0 f = false) : Thm (ax_comprehension f h)
  -- TODO: items 38.x, 39.x, and the axioms of PLM 8.3-8.6. See `AOT/Axioms.lean`.

/-- Derivability from premises. Deliberately *lacks* `rn`. -/
inductive Deriv : List Formula -> Formula -> Prop where
  | ax {G f} : Thm f -> Deriv G f
  | premise {G f} : f ∈ G -> Deriv G f
  | mp {G f g} : Deriv G (imp f g) -> Deriv G f -> Deriv G g
  | gen {G f} : Deriv G f -> Deriv G (alli f)

theorem Thm.toDeriv {G f} (h : Thm f) : Deriv G f := Deriv.ax h

/-
## The two theorems to support

1. **Soundness.** `Thm f -> AOT.valid f`. Requires `AOT/Semantics.lean`.

2. **No modal collapse.** That `Deriv [f] (box f)` does not hold in general,
   i.e. that omitting `rn` from `Deriv` is not merely stylistic. PLM 9.9.3
   treats modal collapse directly. This is the cheapest non-trivial sanity
   check available and should be done early: it needs only soundness plus one
   two-world model.
-/
theorem soundness {f : Formula} (_h : Thm f) : valid f :=
  sorry -- TODO: soundness. Blocked on denoteT/denoteR/denoteF in AOT/Semantics.lean
  -- and on nonempty_model (until that is proved this statement is vacuous).

end AOT
