/-
# axioms of AOT (PLM Ch. 8).

Each axiom is a *schema*: a Lean predicate on formulas, so its side condition
travels with it. PLM 8.10 asserts the universal closures of all of these except
item 43*, of which only the universal closure is asserted.

## Verified against PLM 2026-05-15, pp. 297-301 (= PDF pp. 90-94)

  8.7  item 47      Descriptions
  8.8  item 48.1-.3 alpha-, beta-, eta-Conversion
       item 49      Coexistence of Relations
  8.9  item 50      n-ary Encoding Reduction
       item 51      Rigidity of Encoding
       item 52      Ordinary Objects Fail to Encode Properties
       item 53      Comprehension Principle for Abstract Objects
       item 54      (Remark: the restriction on comprehension)

## NOT YET TRANSCRIBED -- read before using this file for anything

  8.1  Negations and Conditionals        (items 38.x; only 38.1-.2 seen)
  8.2  Quantification and Existence      (items 39.x; 39.2 seen only by reference)
  8.3  Substitution of Identicals
  8.4  Actuality
  8.5  Necessity
  8.6  Necessity and Actuality
-/
import AOT.Defs

namespace AOT
open Formula

/-- A relation term of arity `n` denotes. Abbreviation for readability. -/
abbrev dnR (n : Arity) (P : Rel) : Formula := denotesR n P

/-- PLM item 47: Descriptions.  `y = ix f  ==  Ax(Af == x = y)` -/
def ax_descriptions (f : Formula) : Formula :=
  equiv (eqI (.ivar 0) (.desc f))
        (alli (equiv (act f) (eqI (.ivar 0) (.ivar 1))))

/-- PLM item 48.2: beta-Conversion.
`[L x1..xn f]! -> ([L x1..xn f]x1..xn == f)`

The side condition is the point of this whole development: PLM formulates
beta-Conversion only for matrices that are *exemplification* formulas in the
bound variables. `encPosF i f = false` is the machine-checkable form of that
condition, and it is what keeps `[L z: Ex G(zG & ~Gz)]` (PLM p. 298 fn. 170,
the Clark/Boolos paradox) out of scope. -/
def ax_beta (n : Arity) (f : Formula)
    (_h : forall i, i < n -> encPosF i f = false) : Formula :=
  imp (dnR n (.lam n f))
      (equiv (.exem (.lam n f) ((List.range n).reverse.map Term.ivar)) f)

/-- PLM item 48.3: eta-Conversion.  `[L x1..xn F x1..xn] = F`
Not schematic at all -- it governs only *elementary* lambda-expressions. -/
def ax_eta (n : Arity) (f : Formula) (_h : elementaryMatrix n f = true) : Formula :=
  eqRel n (.lam n f) (.rvar n 0)

/-- PLM item 49: Coexistence of Relations.
`([L x1..xn f]! & Box Ax1..Axn(f == g)) -> [L x1..xn g]!`   (n >= 1)

Note PLM's remark: this is *not* a consequence of the Rules of Substitution
(item 160), and it is what lets one prove significance for some lambda-terms
that item 39.2 excludes -- e.g. `[L xy: O!x & O!y & x = y]!` (theorem 230).
So `g` here is unrestricted, and that is intended. -/
def ax_coexistence (n : Arity) (f g : Formula) : Formula :=
  imp (conj (dnR n (.lam n f))
            (box (alliN n (equiv f g))))
      (dnR n (.lam n g))

/-- PLM item 51: Rigidity of Encoding.  `xF -> Box xF` -/
def ax_enc_rigid : Formula :=
  imp (.enc [.ivar 0] (.rvar 1 0)) (box (.enc [.ivar 0] (.rvar 1 0)))

/-- PLM item 52: Ordinary Objects Fail to Encode Properties.  `O!x -> ~Ex F xF` -/
def ax_ord_no_enc : Formula :=
  imp (.exem Ordinary [.ivar 0])
      (neg (exr 1 (.enc [.ivar 0] (.rvar 1 0))))

/-- PLM item 53: Comprehension Principle for Abstract Objects.
`Ex x(A!x & AF(xF == f))`, **provided `x` does not occur free in `f`**.

Item 54 shows the restriction is not optional: with `f := ~xF` one gets
`Ex x(A!x & AF(xF == ~xF))` and a contradiction on instantiating `F`. Here the
proviso is a hypothesis of the Lean definition, so the bad instance cannot even
be written down. -/
def ax_comprehension (f : Formula) (_h : freeIF 0 f = false) : Formula :=
  exi (conj (.exem Abstract [.ivar 0])
            (allr 1 (equiv (.enc [.ivar 0] (.rvar 1 0)) f)))

/-- PLM item 50: n-ary Encoding Reduction (`n >= 2`).
`x1..xn F == x1[L y: F y x2..xn] & x2[L y: F x1 y x3..xn] & .. & xn[L y: F x1..x(n-1) y]`

TODO: the general `n` case needs the "slot `i` replaced by the fresh bound
variable" construction. Write the `n = 2` instance first and generalise. -/
def ax_enc_reduction (_n : Arity) : Formula :=
  sorry -- TODO: n-ary encoding reduction; needs "slot i replaced by fresh bound
  -- variable". Write the n = 2 instance first, then generalise.

end AOT
