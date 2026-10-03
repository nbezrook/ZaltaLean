/-
# definitions in AOT

!! PLM 8.10 is explicit that `&`, `≡`, `∃`, `O!`, `A!`, `↓` and `=` are *defined*,
not primitive. Keeping them as Lean `def`s over the primitive syntax (rather
than as extra constructors) gives PLM Ch. 9.4 and 9.13: "The
Inferential Role of Definitions" and "...of Definitions-by-`=`"
-/
import AOT.Occurrence

namespace AOT
namespace Formula

def conj (φ ψ : Formula) : Formula := neg (imp φ (neg ψ))
def disj (φ ψ : Formula) : Formula := imp (neg φ) ψ
def equiv (φ ψ : Formula) : Formula := conj (imp φ ψ) (imp ψ φ)
def exi (φ : Formula) : Formula := neg (alli (neg φ))
def exr (n : Arity) (φ : Formula) : Formula := neg (allr n (neg φ))
def dia (φ : Formula) : Formula := neg (box (neg φ))

/-- Universal closure over the first `n` individual variables. -/
def alliN : Nat → Formula → Formula
  | 0, φ => φ
  | n + 1, φ => alliN n (alli φ)

end Formula

open Formula

/-- `O!` =df `[λx ◇E!x]` -- being ordinary. -/
def Ordinary : Rel := .lam 1 (dia (.exem .E [.ivar 0]))

/-- `A!` =df `[λx ¬◇E!x]` -- being abstract. -/
def Abstract : Rel := .lam 1 (neg (dia (.exem .E [.ivar 0])))

/-- `τ↓` for an *individual* term: `∃F Fτ` (PLM 7.2.2, Term Existence in the
Logical Sense). A term denotes just in case something is exemplified by it --
which, given the urrelation condition in `AOT.Frame.Urrel`, fails exactly for
the null objects. -/
def denotesI (τ : Term) : Formula := exr 1 (.exem (.rvar 1 0) [τ])

/-- `Π↓` for a *relation* term. TODO: PLM 7.2.2 gives this via identity
(`∃F(F = Π)`), and `=` for relations is itself defined in 7.2.3 in terms of
encoding (`F = G` iff `∀x(xF ≡ xG)`, modulo the necessity clause). Write
`eqRel` first, then come back. Getting this wrong quietly breaks the whole free
logic, so it is left open rather than guessed. -/
def denotesR (_n : Arity) (_P : Rel) : Formula :=
  sorry -- TODO: PLM 7.2.2 gives this via identity as Ex F(F = P); needs eqRel first.
  -- Read thesis 3.7 (free logic extended to relations) before committing to a form.

/-- `F = G` for relations. TODO as above (PLM 7.2.3). -/
def eqRel (_n : Arity) (_P _P2 : Rel) : Formula :=
  sorry -- TODO: relation identity, PLM 7.2.3: F = G iff Ax(xF == xG), modulo the
  -- necessity clause. Transcribe from the PDF rather than reconstructing it.

/-- `x =_E y`, identity restricted to ordinary objects:
`O!x & O!y & □∀F(Fx ≡ Fy)`. PLM item 231 / theorem 230 -- note that PLM has to
*prove* `[λxy O!x & O!y & x =_E y]↓` (p. 300), since the defining matrix puts a
bound variable in encoding position once the defined terms are expanded. A good
early test case for this development. -/
def eqE (x y : Term) : Formula :=
  conj (conj (.exem Ordinary [x]) (.exem Ordinary [y]))
       (box (allr 1 (equiv (.exem (.rvar 1 0) [x]) (.exem (.rvar 1 0) [y]))))

/-- `x = y` for individuals: `x =_E y ∨ (A!x & A!y & □∀F(xF ≡ yF))`. -/
def eqI (x y : Term) : Formula :=
  disj (eqE x y)
       (conj (conj (.exem Abstract [x]) (.exem Abstract [y]))
             (box (allr 1 (equiv (.enc [x] (.rvar 1 0)) (.enc [y] (.rvar 1 0))))))

end AOT
