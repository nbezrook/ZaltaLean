/-
# Occurrence conditions and substitution.
Two conditions matter most:

* `encPos i φ` -- individual index `i` has an occurrence *in encoding position*
  in `φ`. This is what bars `[λz ∃G(zG & ¬Gz)]` from the scope of β-Conversion
  (PLM item 48.2, p. 298 fn. 170: the Clark/Boolos paradox).

* `freeI i φ` -- individual index `i` occurs free in `φ`. Needed for the
  restriction on Object Comprehension (PLM item 53: `∃x(A!x & ∀F(xF ≡ φ))`
  *provided x doesn't occur free in φ*; item 54 shows that dropping this yields
  a contradiction immediately via `φ := ¬xF`).
-/
import AOT.Syntax

namespace AOT

/-- Is this term literally the individual variable with index `i`? -/
def Term.isIvar (i : Nat) : Term → Bool
  | .ivar j => i == j
  | .desc _ => false

mutual

/-- Occurrence of individual index `i` in encoding position, within a term.
Descends into descriptions, shifting for the binder. -/
def encPosT (i : Nat) : Term → Bool
  | .ivar _ => false
  | .desc φ => encPosF (i + 1) φ

def encPosR (i : Nat) : Rel → Bool
  | .rvar _ _ => false
  | .E => false
  | .lam n φ => encPosF (i + n) φ

def encPosTs (i : Nat) : List Term → Bool
  | [] => false
  | t :: ts => encPosT i t || encPosTs i ts

def encPosF (i : Nat) : Formula → Bool
  | .exem r ts => encPosR i r || encPosTs i ts
  | .enc ts r =>
      -- The slots `ts` *are* the encoding positions.
      ts.any (Term.isIvar i) || encPosR i r || encPosTs i ts
  | .neg φ => encPosF i φ
  | .imp φ ψ => encPosF i φ || encPosF i ψ
  | .alli φ => encPosF (i + 1) φ
  | .allr _ φ => encPosF i φ
  | .box φ => encPosF i φ
  | .act φ => encPosF i φ

end

/-
DESIGN QUESTION, flagged for checking against PLM Ch. 7.1 (Metatheoretical
Definitions): we count an occurrence as *encoding-position* only when the
variable stands in the slot itself, so an occurrence buried inside a description
that sits in an encoding slot (`(ιy φ(x)) F`) does NOT count. PLM states the
condition for variables bound by `λ`; since PLM's encoding takes arbitrary
individual *terms*, this reading looks right, but it is a genuine fork and the
wrong choice here either lets the Clark/Boolos paradox back in or makes the
system weaker than PLM. **Verify before relying on anything downstream.**
-/

mutual

/-- Free occurrence of individual index `i`. -/
def freeIT (i : Nat) : Term → Bool
  | .ivar j => i == j
  | .desc φ => freeIF (i + 1) φ

def freeIR (i : Nat) : Rel → Bool
  | .rvar _ _ => false
  | .E => false
  | .lam n φ => freeIF (i + n) φ

def freeITs (i : Nat) : List Term → Bool
  | [] => false
  | t :: ts => freeIT i t || freeITs i ts

def freeIF (i : Nat) : Formula → Bool
  | .exem r ts => freeIR i r || freeITs i ts
  | .enc ts r => freeITs i ts || freeIR i r
  | .neg φ => freeIF i φ
  | .imp φ ψ => freeIF i φ || freeIF i ψ
  | .alli φ => freeIF (i + 1) φ
  | .allr _ φ => freeIF i φ
  | .box φ => freeIF i φ
  | .act φ => freeIF i φ

end

/-- `ts` is exactly the sequence of bound variables of an `n`-ary λ, in order:
under de Bruijn, `x₁…xₙ` is `[ivar (n-1), …, ivar 0]`. -/
def isIvarSeq : Nat → List Term → Bool
  | _, [] => true
  | k, t :: ts => Term.isIvar k t && isIvarSeq (k - 1) ts

/-- An *elementary* matrix for an `n`-ary λ: an exemplification formula whose
arguments are exactly the bound variables, in order. This is the shape
η-Conversion governs (PLM item 48.3: `[λx₁…xₙ F^n x₁…xₙ] = F^n`). -/
def elementaryMatrix (n : Nat) : Formula → Bool
  | .exem (.rvar m _) ts =>
      m == n && ts.length == n && isIvarSeq (n - 1) ts
  | _ => false

/-- Index shifting (de Bruijn lifting) for individual indices.
TODO: needed before substitution; left unimplemented so that no downstream file
silently depends on a wrong definition. -/
def shiftI (_cutoff : Nat) (_by : Nat) : Formula → Formula :=
  sorry -- TODO: de Bruijn lifting. Must shift under alli, desc (by 1) and lam n (by n);
  -- allr binds a relation variable and so must NOT shift individual indices.

/-- Substitution of an individual term for individual index `i`.
TODO: implement alongside `shiftI`, then prove the standard commutation lemmas
(`substI_shiftI`, `freeIF_substI`, `encPosF_substI`). These lemmas are the real
content: PLM's Rules of Substitution (item 160) and its catalogue of
*illegitimate* uses (item 161) are exactly statements about substitution
interacting with modal strictness, and they are what a deep embedding lets us
check. -/
def substI (_i : Nat) (_s : Term) : Formula → Formula :=
  sorry -- TODO: substitution, with shiftI. Then prove substI_shiftI, freeIF_substI,
  -- encPosF_substI -- these are the real content: PLM item 160 (Rules of Substitution)
  -- and item 161 (illegitimate uses) are statements about exactly this interaction.

end AOT
