-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.SubstLemmas
/-!
# L1 soundness: `DefEq t (embNf (nf t))` (ET-2, milestone 2 of MECH-1)

The substitution-commutation family at the `DefEq` level — the lemma named
in Conversion.lean's docstring,
`DefEq (substTy (embNf t) x (embNf u)) (embNf (substNf t x u))` — proved by
the same `(kindSize, tag, size)` lexicographic induction as `substNf`
itself. `DefEq`'s β-rule absorbs all the β-work `appSp` performs, so this
direction needs no equational commutation of substitutions. Soundness of
the normalizer follows by structural induction.
-/

namespace Systemet.L1

mutual
  /-- Substitution commutes with embedding, up to conversion: the
      Keller–Altenkirch commutation lemma at the `DefEq` level. -/
  theorem defEq_substTy_embNf : {Γ : Ctx} → {j k : Kind} → (t : Nf Γ j) →
      (x : Var Γ k) → (u : Nf (rem x) k) →
      DefEq (substTy (embNf t) x (embNf u)) (embNf (substNf t x u))
    | _, _, _, .lam (k₁ := k₁) b, x, u => by
      have ih := defEq_substTy_embNf b (Var.vs (k' := k₁) x) (wkNf .vz u)
      rw [embNf_wkNf] at ih
      simp only [embNf, substNf, substTy]
      exact ih.lamCong
    | _, _, _, .base n, _, _ => by
      simp only [embNf, substNf, substTy]
      exact .refl
    | _, _, _, .arrow a b, x, u => by
      simp only [embNf, substNf, substTy]
      exact (defEq_substTy_embNf a x u).arrowCong (defEq_substTy_embNf b x u)
    | _, _, _, .ne (k := c) z sp, x, u =>
      match c, z, sp, eqv x z with
      | _, _, sp, .same => by
        simp only [embNf, substNf_ne_self]
        exact (defEq_substTy_embSp sp x u (.var x) (embNf u)
          (by simp only [substTy, eqv_refl]; exact .refl)).trans
          (defEq_embSp_appSp u (substSp sp x u))
      | _, _, sp, .diff _ z' => by
        simp only [embNf, substNf_ne_wkv]
        exact defEq_substTy_embSp sp x u (.var (wkv x z')) (.var z')
          (by simp only [substTy, eqv_wkv]; exact .refl)
  termination_by _ _ k t _ _ => (kindSize k, 1, nfSize t)
  decreasing_by
    all_goals simp only [nfSize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.right; apply Prod.Lex.left; omega)

  /-- Spine form of `defEq_substTy_embNf`, threading a converted head. -/
  theorem defEq_substTy_embSp : {Γ : Ctx} → {a j k : Kind} → (sp : Sp Γ a j) →
      (x : Var Γ k) → (u : Nf (rem x) k) → (h : Ty Γ a) → (h' : Ty (rem x) a) →
      DefEq (substTy h x (embNf u)) h' →
      DefEq (substTy (embSp h sp) x (embNf u)) (embSp h' (substSp sp x u))
    | _, _, _, _, .nil, _, _, _, _, hh => by
      simp only [embSp, substSp]
      exact hh
    | _, _, _, _, .cons sp v, x, u, h, h', hh => by
      simp only [embSp, substSp, substTy]
      exact (defEq_substTy_embSp sp x u h h' hh).appCong
        (defEq_substTy_embNf v x u)
  termination_by _ _ _ k sp _ _ _ _ _ => (kindSize k, 1, spSize sp)
  decreasing_by
    all_goals simp only [spSize]
    all_goals (apply Prod.Lex.right; apply Prod.Lex.right; omega)

  /-- Folding a normal form through a spine, embedded: `appSp` is
      conversion-compatible. -/
  theorem defEq_embSp_appSp : {Γ : Ctx} → {a j : Kind} → (F : Nf Γ a) →
      (SP : Sp Γ a j) → DefEq (embSp (embNf F) SP) (embNf (appSp F SP))
    | _, _, _, F, .nil => by
      simp only [embSp, appSp]
      exact .refl
    | _, _, _, F, .cons SP v => by
      rw [appSp_cons]
      have s1 := (defEq_embSp_appSp F SP).appCong (DefEq.refl (t := embNf v))
      cases hG : appSp F SP with
      | lam T =>
        rw [hG] at s1
        simp only [embSp, embNf, napp] at s1 ⊢
        exact s1.trans ((DefEq.beta (embNf T) (embNf v)).trans
          (defEq_substTy_embNf T .vz v))
      | ne y sp' =>
        rw [hG] at s1
        simp only [embSp, embNf, napp] at s1 ⊢
        exact s1
  termination_by _ a _ _ SP => (kindSize a, 0, spSize SP)
  decreasing_by
    all_goals simp only [spSize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left
         have h := spKindLe SP
         simp only [kindSize] at h ⊢
         omega)
end

/-- One-step β-application, embedded: `napp` is conversion-compatible. -/
theorem defEq_embNf_napp : {Γ : Ctx} → {a b : Kind} → (F : Nf Γ (.arr a b)) →
    (A : Nf Γ a) → DefEq (.app (embNf F) (embNf A)) (embNf (napp F A))
  | _, _, _, .lam T, A => by
    simp only [embNf, napp]
    exact (DefEq.beta (embNf T) (embNf A)).trans (defEq_substTy_embNf T .vz A)
  | _, _, _, .ne y sp, A => by
    simp only [embNf, napp, embSp]
    exact .refl

/-- **Soundness**: every type-level term converts to its normal form.
    With stability (`nf_emb`) this makes `nf` a normalizer for `DefEq`. -/
theorem soundness : {Γ : Ctx} → {k : Kind} → (t : Ty Γ k) → DefEq t (embNf (nf t))
  | _, _, .var x => by
    simp only [nf, embNf, embSp]
    exact .refl
  | _, _, .base n => by
    simp only [nf, embNf]
    exact .refl
  | _, _, .arrow a b => by
    simp only [nf, embNf]
    exact (soundness a).arrowCong (soundness b)
  | _, _, .lam b => by
    simp only [nf, embNf]
    exact (soundness b).lamCong
  | _, _, .app f a => by
    simp only [nf]
    exact ((soundness f).appCong (soundness a)).trans
      (defEq_embNf_napp (nf f) (nf a))
termination_by _ _ t => tySize t
decreasing_by all_goals (simp only [tySize]; first | exact Nat.lt_succ_self _ | omega)

end Systemet.L1
