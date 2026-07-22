-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.Soundness
/-!
# L1 completeness and `defEq_iff_nf` (ET-2)

Completeness — convertible terms have equal normal forms — by induction on
the conversion derivation; the β-case is exactly the commutation equation
`nf_substTy`. Together with soundness this gives the ET-2 headline
`defEq_iff_nf : DefEq t u ↔ nf t = nf u`.
-/

namespace Systemet.L1

/-- **Completeness**: `nf` respects conversion. -/
theorem completeness : {Γ : Ctx} → {k : Kind} → {t u : Ty Γ k} →
    DefEq t u → nf t = nf u := by
  intro Γ k t u h
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | beta b u =>
    show nf (.app (.lam b) u) = nf (subst0 b u)
    simp only [nf, napp]
    exact (nf_substTy b .vz u).symm
  | arrowCong _ _ ih₁ ih₂ =>
    simp only [nf]
    rw [ih₁, ih₂]
  | lamCong _ ih =>
    simp only [nf]
    rw [ih]
  | appCong _ _ ih₁ ih₂ =>
    simp only [nf]
    rw [ih₁, ih₂]

/-- **ET-2, headline**: conversion is normalize-then-compare. -/
theorem defEq_iff_nf {Γ : Ctx} {k : Kind} {t u : Ty Γ k} :
    DefEq t u ↔ nf t = nf u :=
  ⟨completeness, fun h =>
    (soundness t).trans (by
      rw [congrArg embNf h]
      exact (soundness u).symm)⟩

end Systemet.L1
