-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.EtaHsub
import Systemet.L1.Conversion
/-!
# L1 βη-conversion (ET-η: the extended primitive relation)

`DefEqE` is `DefEq` plus the η-rule: a term `t` at kind `k₁ ⇒ k₂` is
convertible with `λ. (↑t) a₀` — its η-expansion, where `↑` is weakening by
the fresh slot (`wkTy .vz`) and `a₀` is the fresh variable (`.var .vz`).
The rules are otherwise verbatim `DefEq`, so `DefEqE` is again the least
congruent equivalence containing β — now also containing η.

`defEq_to_defEqE` embeds the β-theory: η strictly extends it.
-/

namespace Systemet.L1

/-- Declarative βη-conversion: the least congruent equivalence containing
    β and η. -/
inductive DefEqE : {Γ : Ctx} → {k : Kind} → Ty Γ k → Ty Γ k → Prop where
  | refl      : DefEqE t t
  | symm      : DefEqE t u → DefEqE u t
  | trans     : DefEqE t u → DefEqE u v → DefEqE t v
  | beta      : (b : Ty (k₁ :: Γ) k₂) → (u : Ty Γ k₁) →
                DefEqE (.app (.lam b) u) (subst0 b u)
  | eta       : (t : Ty Γ (.arr k₁ k₂)) →
                DefEqE t (.lam (.app (wkTy .vz t) (.var .vz)))
  | arrowCong : DefEqE a a' → DefEqE b b' → DefEqE (.arrow a b) (.arrow a' b')
  | lamCong   : DefEqE b b' → DefEqE (.lam b) (.lam b')
  | appCong   : DefEqE f f' → DefEqE a a' → DefEqE (.app f a) (.app f' a')

/-- β-conversion embeds into βη-conversion: η strictly extends β. -/
theorem defEq_to_defEqE {Γ : Ctx} {k : Kind} {t u : Ty Γ k} :
    DefEq t u → DefEqE t u := by
  intro h
  induction h with
  | refl => exact .refl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | beta b u => exact .beta b u
  | arrowCong _ _ ih₁ ih₂ => exact ih₁.arrowCong ih₂
  | lamCong _ ih => exact ih.lamCong
  | appCong _ _ ih₁ ih₂ => exact ih₁.appCong ih₂

end Systemet.L1
