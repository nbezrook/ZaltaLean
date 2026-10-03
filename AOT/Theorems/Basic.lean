/-
# basic theorems of AOT (PLM Ch. 9).

Each gap carries an inline `sorry -- TODO:` saying what remains, so grepping for `sorry` finds the
description rather than just the hole.
-/
import AOT.Deduction

namespace AOT
open Formula

/-- PLM 9.11.1: an ordinary object necessarily fails to encode anything.
`O!x -> Box ~Ex F xF`.  Needs: the modal axioms of PLM 8.5-8.6. -/
theorem ord_nec_no_enc :
    Thm (alliN 1 (imp (.exem Ordinary [.ivar 0])
                       (box (neg (exr 1 (.enc [.ivar 0] (.rvar 1 0))))))) :=
  sorry -- TODO: needs the modal axioms of PLM 8.5-8.6, not yet transcribed.

/-- PLM item 111.2: `[L f] == f` *unconditionally* for 0-ary lambda.
PLM notes this is derivable without the 0-ary case of beta-Conversion -- a good
test that our restriction bookkeeping is neither too strong nor too weak. -/
theorem lam0_equiv (f : Formula) :
    Thm (equiv (.exem (.lam 0 f) []) f) :=
  sorry -- TODO: PLM item 111.2. Must go through WITHOUT the 0-ary case of beta-
  -- Conversion; if it needs it, our restriction bookkeeping is too strong.

/-- PLM theorem 230: `[L xy: O!x & O!y & x =E y]!`.
The interesting one. The matrix puts bound variables in encoding position once
`=E` is expanded, so beta-Conversion does *not* apply; significance has to come
via Coexistence (item 49) from a matrix that is necessarily equivalent. If this
goes through, the free-logic layer is working. -/
theorem eqE_lam_denotes :
    Thm (denotesR 2 (.lam 2 (conj (conj (.exem Ordinary [.ivar 1])
                                        (.exem Ordinary [.ivar 0]))
                                  (eqE (.ivar 1) (.ivar 0))))) :=
  sorry -- TODO: PLM theorem 230, via Coexistence (item 49), NOT beta-Conversion --
  -- the matrix puts bound variables in encoding position once =E is expanded.

/-- The Clark/Boolos term does not denote: `~[L z: Ex G(zG & ~Gz)]!`.
PLM p. 298 fn. 170 / p. 299. Proving this -- rather than making it
unstateable -- is the test that the deep embedding is faithful. -/
theorem clark_boolos_fails :
    Thm (neg (denotesR 1
      (.lam 1 (exr 1 (conj (.enc [.ivar 0] (.rvar 1 0))
                           (neg (.exem (.rvar 1 0) [.ivar 0]))))))) :=
  sorry -- TODO: the faithfulness test. The Clark/Boolos term is WRITABLE in our
  -- syntax and must be PROVABLY non-denoting (PLM p. 298 fn. 170, p. 299).

end AOT
