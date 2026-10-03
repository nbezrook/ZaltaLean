/-
# aczel-style models
port of `AOT_model.thy` (Kirchner, thesis App. A.1 / 4.1)

whole frame is a `structure`. `Nonempty Frame`, proved
by exhibiting `stdFrame`. every later result must be a statement
*about frames*
-/

/- TODO:
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Basic.Countable.Defs

namespace AOT

/-- An Aczel-style frame for AOT. -/
structure Frame where
  /-- `ο`: hyperintensional propositions. Distinct propositions may share a
  truth condition, which is what makes relation identity finer than necessary
  equivalence. -/
  Prp : Type
  /-- Possible worlds. -/
  W : Type
  /-- The Montague intension of a proposition. -/
  dp : Prp → (W → Prop)
  /-- Surjectivity: every truth condition is realised by some proposition.
  Gives the proposition-choice operator `εₒ`. -/
  dp_surj : Function.Surjective dp
  /-- The designated actual world. -/
  w0 : W
  /-- PLM's axioms require a non-actual world (needed for `𝒜` to be
  non-trivial, PLM 8.4/8.6). -/
  nonactual : ∃ w, w ≠ w0
  /-- `ω`: ordinary urelements. -/
  Om : Type
  /-- `σ`: special urelements, the images of abstract objects. In the Isabelle
  model this is `σ' ⊕ ℕ ⊕ {∞}`, the extra summands being what makes *extended*
  relation comprehension and the Frege construction go through. -/
  Sg : Type
  /-- Null urelements, representing non-denoting terms. Several distinct
  necessarily-false propositions may exist, so this is a type, not a point. -/
  Nul : Type
  [inhabited_W : Inhabited W]

attribute [instance] Frame.inhabited_W

namespace Frame

variable (F : Frame)

/-- Validity of a proposition at a world. -/
def validIn (w : F.W) (p : F.Prp) : Prop := F.dp p w

/-- `υ`: urelements. -/
inductive Ur (F : Frame) where
  | ord : F.Om → Ur F
  | spec : F.Sg → Ur F
  | null : F.Nul → Ur F

/-- Is this urelement a null urelement? -/
def Ur.isNull : F.Ur → Prop
  | .null _ => True
  | _ => False

/-- *Urrelations*: proposition-valued functions on urelements that are
necessarily false at every null urelement. This clause is what makes the free
logic work: a non-denoting term is sent to a null urelement, and every relation
fails of it at every world. -/
def Urrel := { f : F.Ur → F.Prp // ∀ (n : F.Nul) (w : F.W), ¬ F.validIn w (f (.null n)) }

/-- Individual objects: ordinary objects are urelements; abstract objects *are*
sets of urrelations (the ones they encode); null objects stand in for
non-denoting descriptions. -/
inductive Obj (F : Frame) where
  | ord : F.Om → Obj F
  | abs : Set F.Urrel → Obj F
  | null : F.Nul → Obj F

end Frame

/-- A frame together with the mapping `ασ` that sends each abstract object to
its special urelement. Keeping this separate from `Frame` matters: *which*
`alphaSigma` you pick is exactly what decides whether extended relation
comprehension holds (Kirchner thesis §4.1, §5.20 "Modelling Possible Richness
of Objects"), so it is a parameter to be varied, not part of the frame. -/
structure Model extends Frame where
  alphaSigma : Set toFrame.Urrel → toFrame.Sg
  /-- The simple models only require surjectivity. Stronger conditions give
  extended comprehension. -/
  alphaSigma_surj : Function.Surjective alphaSigma

namespace Model

variable (M : Model)

/-- Every individual object determines an urelement. -/
def urOf : M.Obj → M.Ur
  | .ord o => .ord o
  | .abs s => .spec (M.alphaSigma s)
  | .null n => .null n

end Model

/-
## what to do next

`stdFrame` / `stdModel` below are the Lean counterpart of Isabelle's
`nitpick[satisfy]` check, and the single most important thing to discharge
first: until it is proved, every theorem in this development is vacuous.

Sketch: take `W := Bool` (so `w0 := false` and `true ≠ w0` witnesses
`nonactual`); take `Prp := (W → Prop) × ℕ` with `dp := Prod.fst` -- the `ℕ`
component is what buys hyperintensionality, giving countably many distinct
propositions per truth condition, and `dp_surj` is then immediate. Take
`Om := Unit`, `Nul := Unit`, and `Sg := Set F.Urrel` with `alphaSigma := id`,
which makes `alphaSigma_surj` trivial.

The one thing to check is that `Sg := Set Urrel` is not circular: `Urrel`
mentions `Ur`, which mentions `Sg`. It is -- which is precisely the
cardinality problem the Aczel construction exists to solve, and why the Isabelle
model uses a *countable* `σ'` plus `ℕ` plus `∞` rather than the full powerset.
Expect to need `Mathlib.SetTheory.Cardinal` and a bounded-set construction
mirroring `HOL-Cardinals.Bounded_Set`. Do not paper over this.
-/
theorem nonempty_frame : Nonempty Frame :=
  sorry -- TODO: exhibit a frame. Sketch in the comment above; the real obstacle is
  -- the circularity Sg ~ Set Urrel, which is why Isabelle uses countable sigma-prime
  -- plus Nat plus infinity rather than the full powerset. Needs Mathlib Cardinal.

theorem nonempty_model : Nonempty Model :=
  sorry -- TODO: as nonempty_frame, plus a choice of alphaSigma that is surjective.
  -- LOAD-BEARING: until this is proved every theorem in this development is vacuous.

end AOT
