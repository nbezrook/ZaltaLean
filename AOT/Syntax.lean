/-
# The object language of AOT, as a deep embedding.

PLM (2026-05-15), Ch. 7 "The Language" Ch. 8 "The Axioms".

*primitive* notions:

    F^n x₁…xₙ   (exemplification)
    x₁…xₙ F^n   (encoding)
    E!          (the sole primitive relation constant)
    ¬  →  ∀  □  𝒜  ι  λ

while `&`, `≡`, `∃`, `O!`, `A!`, `↓` and `=` are all *defined*. mirror that
split exactly. this file declares primitives and `AOT/Defs.lean`
introduces the defined notions as abbreviations.

## syntax restrictions

PLM's β-Conversion ( 48.2) holds onl for λ-expressions whose matrix is an
*exemplification* formula in the bound variables. abstracting over a variable
in *encoding* position is barred on pain of Clark/Boolos paradox (PLM
p. 298 fn. 170). PLM's own language *permits* writing `[λz ∃G(zG & ¬Gz)]`.

side conditions in `AOT/Occurrence.lean` as decidable `Prop`s.
-/

namespace AOT

/-- Arity of a relation. `0` is admitted: 0-ary relations are propositions
(PLM 8.8 discusses the 0-ary cases of α-, β- and η-Conversion separately). -/
abbrev Arity := Nat

mutual

/-- Individual terms. De Bruijn: `ivar i` refers to the `i`-th enclosing
individual binder (`∀x`, `ιx`, or a `λ`). -/
inductive Term where
  /-- Individual variable, de Bruijn index. -/
  | ivar : Nat → Term
  /-- `ιx φ`, the rigid definite description. Binds individual index `0` in `φ`.
  May fail to denote (PLM 8.7). -/
  | desc : Formula → Term


/-- Relation terms of some arity. The arity is carried as data; `AOT/Wf.lean`
checks that it agrees with the argument lists at each application site. -/
inductive Rel where
  /-- Relation variable: `rvar n i` is the `i`-th enclosing relation binder, of
  arity `n`. -/
  | rvar : Arity → Nat → Rel
  /-- `E!`, the primitive relation constant (being concrete). Arity 1. -/
  | E : Rel
  /-- `[λx₁…xₙ φ]`. Binds `n` individual indices in `φ`. Unrestricted here;
  significance is decided by `Denotes` (see the design note above). -/
  | lam : Arity → Formula → Rel


/-- Formulas. -/
inductive Formula where
  /-- `Π t₁…tₙ` -- exemplification. -/
  | exem : Rel → List Term → Formula
  /-- `t₁…tₙ Π` -- encoding. PLM 8.9 item 50 reduces the `n ≥ 2` case to unary
  encodings, but keeps n-ary encoding primitive so that `1 < 2` and
  `Holmes is a friend of Watson` get a genuinely relational reading. -/
  | enc : List Term → Rel → Formula
  | neg : Formula → Formula
  | imp : Formula → Formula → Formula
  /-- `∀x φ` -- binds individual index `0`. -/
  | alli : Formula → Formula
  /-- `∀F^n φ` -- binds relation index `0` at arity `n`. -/
  | allr : Arity → Formula → Formula
  /-- `□φ`. -/
  | box : Formula → Formula
  /-- `𝒜φ` -- "it is actually the case that". Not interdefinable with `□`;
  PLM 8.6 relates them by separate axioms. -/
  | act : Formula → Formula


end

end AOT

/-
NOTE (unverified): `deriving Repr`/`DecidableEq` across a *mutual* nested
inductive is the first thing to check once a toolchain is installed. If the
deriving handlers balk, write the instances by hand in `AOT/Instances.lean`
rather than flattening the mutual block -- the three-sort split mirrors PLM's
own grammar and is worth keeping.
-/
