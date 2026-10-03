/-
TODO: explain the semantics of the AOT language, including the denotation of terms, relations, and formulas, as well as the satisfaction relation and validity. This file defines the necessary structures and functions to interpret the AOT language within a given model.
-/
import AOT.Defs
import AOT.Model

namespace AOT

variable (M : Model)

/-- `n`-ary urrelations: proposition-valued functions on `n`-tuples of
urelements, necessarily false whenever any argument is a null urelement. -/
def Urrel' (n : Arity) :=
  { f : (Fin n → M.Ur) → M.Prp //
      ∀ (args : Fin n → M.Ur) (w : M.W), (∃ i, (args i).isNull) → ¬ M.validIn w (f args) }

/-- Variable assignment. De Bruijn means these are lists, consumed as binders
are crossed. -/
structure Assignment (M : Model) where
  ind : Nat → M.Obj
  rel : (n : Arity) → Nat → Urrel' M n

/-- Denotation of an individual term. Non-denoting descriptions land on a null
object -- this is the negative free logic, made explicit. -/
def denoteT (g : Assignment M) : Term → M.Obj :=
  sorry -- TODO: individual denotation. Non-denoting descriptions must land on a null
  -- object -- that is the negative free logic.

/-- Denotation of a relation term. `[λx₁…xₙ φ]` denotes a genuine urrelation
when the matrix is admissible (see `encPosF`) and a *null*-valued one otherwise,
so that `Π↓` fails exactly where PLM says it does. -/
def denoteR (g : Assignment M) (n : Arity) : Rel → Urrel' M n :=
  sorry -- TODO: relation denotation. A lam must yield a genuine urrelation when the
  -- matrix is admissible (see encPosF) and a null-valued one otherwise, so that P!
  -- fails exactly where PLM says it does.

/-- Denotation of a formula as a hyperintensional proposition (not a truth
value, and not a set of worlds -- that is the whole point). -/
def denoteF (g : Assignment M) : Formula → M.Prp :=
  sorry -- TODO: formula denotation, into Prp (a hyperintensional proposition), NOT a
  -- truth value and NOT a set of worlds -- that is the whole point of the Prp type.

/-- Truth at a world. -/
def satisfies (g : Assignment M) (w : M.W) (φ : Formula) : Prop :=
  M.validIn w (denoteF M g φ)

/-- Truth simpliciter: truth at the designated actual world. -/
def valid (φ : Formula) : Prop :=
  ∀ (M : Model) (g : Assignment M), satisfies M g M.w0 φ

end AOT
