-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.EtaHsub
import Systemet.L1.SubstLemmas
/-!
# L1 substitution-commutation toolkit for η-long forms

The Keller–Altenkirch commutation-lemma base of `SubstLemmas.lean`, ported
to `NfE`/`SpE`. The variable-level laws (`eqv_refl`, `eqv_wkv`, `swp`,
`remSwap`, `wkv_wkv`, the `castV` kit and the lexicographic-descent
helpers) are *reused* from `SubstLemmas.lean` — they mention only `Var`.
What is ported here: the `castNfE`/`castSpE` transport kit, the spine
computation laws, commutation of the embeddings with weakening, the
cancellation law, the exchange of weakenings, and the
weakening/substitution exchange. The η-restriction only shrinks proofs:
`appSpE`'s intermediate forms at arrow kinds are always `lam`s, so every
neutral-function branch of the β-fold disappears.
-/

namespace Systemet.L1

/-! ## Spine application unrolling -/

/-- `appSpE` peels its last argument through `nappE`. -/
theorem appSpE_cons (u : NfE Γ a) (sp : SpE Γ a (.arr b c)) (v : NfE Γ b) :
    appSpE u (.cons sp v) = nappE (appSpE u sp) v := by
  cases h : appSpE u sp with
  | lam t => simp [appSpE, nappE, h]

/-- `substNfE` at the substituted head: hand off to the spine fold. -/
theorem substNfE_ne_self (x : Var Γ k) (sp : SpE Γ k .star) (u : NfE (rem x) k) :
    substNfE (.ne x sp) x u = appSpE u (substSpE sp x u) := by
  simp [substNfE, eqv_refl]

/-- `substNfE` at a missed head: keep the neutral. -/
theorem substNfE_ne_wkv (x : Var Γ k) (y : Var (rem x) c) (sp : SpE Γ c .star)
    (u : NfE (rem x) k) :
    substNfE (.ne (wkv x y) sp) x u = .ne y (substSpE sp x u) := by
  simp [substNfE, eqv_wkv]

/-! ## Embedding commutes with weakening -/

mutual
  /-- Embedding a weakened η-long form is weakening the embedding. -/
  theorem embNfE_wkNfE : {Γ : Ctx} → {c j : Kind} → (x : Var Γ c) → (t : NfE (rem x) j) →
      embNfE (wkNfE x t) = wkTy x (embNfE t)
    | _, _, _, x, .lam (k₁ := k₁) b => by
      simp only [wkNfE, embNfE, wkTy]
      exact congrArg Ty.lam (embNfE_wkNfE (Var.vs (k' := k₁) x) b)
    | _, _, _, _, .base n => by simp [wkNfE, embNfE, wkTy]
    | _, _, _, x, .arrow a b => by
      simp [wkNfE, embNfE, wkTy, embNfE_wkNfE x a, embNfE_wkNfE x b]
    | _, _, _, x, .ne y sp => by
      have h := embSpE_wkSpE x (.var y) sp
      simp only [wkTy] at h
      simp [wkNfE, embNfE, h]
  termination_by _ _ _ _ t => nfESize t
  decreasing_by all_goals (simp only [nfESize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Spine form of `embNfE_wkNfE`. -/
  theorem embSpE_wkSpE : {Γ : Ctx} → {c a j : Kind} → (x : Var Γ c) → (h : Ty (rem x) a) →
      (sp : SpE (rem x) a j) → embSpE (wkTy x h) (wkSpE x sp) = wkTy x (embSpE h sp)
    | _, _, _, _, _, _, .nil => by simp [wkSpE, embSpE]
    | _, _, _, _, x, h, .cons sp v => by
      simp [wkSpE, embSpE, wkTy, embSpE_wkSpE x h sp, embNfE_wkNfE x v]
  termination_by _ _ _ _ _ _ sp => spESize sp
  decreasing_by all_goals (simp only [spESize]; omega)
end

/-! ## Cancellation: substituting a freshly weakened form -/

mutual
  /-- Substituting at a slot the form was just weakened past is the identity. -/
  theorem substNfE_wkNfE_cancel : {Γ : Ctx} → {k j : Kind} → (x : Var Γ k) →
      (t : NfE (rem x) j) → (u : NfE (rem x) k) → substNfE (wkNfE x t) x u = t
    | _, _, _, x, .lam (k₁ := k₁) b, u => by
      simp only [wkNfE, substNfE]
      exact congrArg NfE.lam
        (substNfE_wkNfE_cancel (Var.vs (k' := k₁) x) b (wkNfE .vz u))
    | _, _, _, _, .base n, _ => by simp [wkNfE, substNfE]
    | _, _, _, x, .arrow a b, u => by
      simp [wkNfE, substNfE, substNfE_wkNfE_cancel x a u, substNfE_wkNfE_cancel x b u]
    | _, _, _, x, .ne y sp, u => by
      simp [wkNfE, substNfE_ne_wkv, substSpE_wkSpE_cancel x sp u]
  termination_by _ _ _ _ t _ => nfESize t
  decreasing_by all_goals (simp only [nfESize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Spine form of `substNfE_wkNfE_cancel`. -/
  theorem substSpE_wkSpE_cancel : {Γ : Ctx} → {k a j : Kind} → (x : Var Γ k) →
      (sp : SpE (rem x) a j) → (u : NfE (rem x) k) → substSpE (wkSpE x sp) x u = sp
    | _, _, _, _, _, .nil, _ => by simp [wkSpE, substSpE]
    | _, _, _, _, x, .cons sp v, u => by
      simp [wkSpE, substSpE, substSpE_wkSpE_cancel x sp u, substNfE_wkNfE_cancel x v u]
  termination_by _ _ _ _ _ sp _ => spESize sp
  decreasing_by all_goals (simp only [spESize]; omega)
end

/-! ## Context-cast toolkit for η-long forms -/

/-- Transport an η-long form along a context equality. -/
def castNfE (h : Δ = Δ') (t : NfE Δ j) : NfE Δ' j := h ▸ t

/-- Transport a spine along a context equality. -/
def castSpE (h : Δ = Δ') (s : SpE Δ a j) : SpE Δ' a j := h ▸ s

theorem castNfE_diag (e : Δ = Δ) (t : NfE Δ j) : castNfE e t = t := rfl

theorem castSpE_diag (e : Δ = Δ) (s : SpE Δ a j) : castSpE e s = s := rfl

theorem castNfE_lam (h : Δ = Δ') (b : NfE (k₁ :: Δ) k₂) :
    castNfE h (.lam b) = .lam (castNfE (congrArg (k₁ :: ·) h) b) := by
  subst h; rfl

theorem castNfE_base (h : Δ = Δ') (n : Nat) :
    castNfE h (.base n) = .base n := by
  subst h; rfl

theorem castNfE_arrow (h : Δ = Δ') (a b : NfE Δ .star) :
    castNfE h (.arrow a b) = .arrow (castNfE h a) (castNfE h b) := by
  subst h; rfl

theorem castNfE_ne (h : Δ = Δ') (y : Var Δ c) (sp : SpE Δ c .star) :
    castNfE h (.ne y sp) = .ne (castV h y) (castSpE h sp) := by
  subst h; rfl

theorem castSpE_nil (h : Δ = Δ') :
    castSpE h (.nil (Γ := Δ) (k := a)) = .nil := by
  subst h; rfl

theorem castSpE_cons (h : Δ = Δ') (sp : SpE Δ a (.arr b c)) (v : NfE Δ b) :
    castSpE h (.cons sp v) = .cons (castSpE h sp) (castNfE h v) := by
  subst h; rfl

theorem castNfE_appSpE (h : Δ = Δ') (F : NfE Δ a) (SP : SpE Δ a j) :
    castNfE h (appSpE F SP) = appSpE (castNfE h F) (castSpE h SP) := by
  subst h; rfl

theorem castNfE_castNfE (e : Δ = Δ') (e' : Δ' = Δ'') (t : NfE Δ j) :
    castNfE e' (castNfE e t) = castNfE (e.trans e') t := by
  subst e; subst e'; rfl

/-- Transporting past a fresh top slot commutes with weakening at `vz`. -/
theorem castNfE_wkNfE_vz (h : Δ = Δ') (e : (c :: Δ : Ctx) = c :: Δ') (t : NfE Δ j) :
    castNfE e (wkNfE (.vz (k := c) (Γ := Δ)) t) = wkNfE .vz (castNfE h t) := by
  subst h; rfl

/-- Spine form of `castNfE_wkNfE_vz`. -/
theorem castSpE_wkSpE_vz (h : Δ = Δ') (e : (c :: Δ : Ctx) = c :: Δ') (sp : SpE Δ a j) :
    castSpE e (wkSpE (.vz (k := c) (Γ := Δ)) sp) = wkSpE .vz (castSpE h sp) := by
  subst h; rfl

theorem castNfE_symm_cancel (e : Δ = Δ') (t : NfE Δ' j) :
    castNfE e (castNfE e.symm t) = t := by
  subst e; rfl

theorem castSpE_symm_cancel (e : Δ = Δ') (sp : SpE Δ' a j) :
    castSpE e (castSpE e.symm sp) = sp := by
  subst e; rfl

/-- η-expansion transports along a context equality. -/
theorem castNfE_etaNe (h : Δ = Δ') (j : Kind) (x : Var Δ a) (sp : SpE Δ a j) :
    castNfE h (etaNe j x sp) = etaNe j (castV h x) (castSpE h sp) := by
  subst h; rfl

/-! ## Exchange of weakenings -/

mutual
  /-- Exchange of weakenings on η-long forms. -/
  theorem wkNfE_wkNfE : {Γ : Ctx} → {k c j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) c) → (t : NfE (rem y) j) →
      wkNfE x (wkNfE y t) =
        wkNfE (wkv x y) (wkNfE (swp x y) (castNfE (remSwap x y).symm t))
    | _, _, _, _, x, y, .lam (k₁ := k₁) b => by
      rw [castNfE_lam]
      simp only [wkNfE]
      exact congrArg NfE.lam
        (wkNfE_wkNfE (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y) b)
    | _, _, _, _, x, y, .base n => by
      rw [castNfE_base]
      simp [wkNfE]
    | _, _, _, _, x, y, .arrow a b => by
      rw [castNfE_arrow]
      simp only [wkNfE]
      rw [wkNfE_wkNfE x y a, wkNfE_wkNfE x y b]
    | _, _, _, _, x, y, .ne z sp => by
      rw [castNfE_ne]
      simp only [wkNfE]
      rw [wkv_wkv x y z, wkSpE_wkSpE x y sp]
  termination_by _ _ _ _ _ _ t => nfESize t
  decreasing_by all_goals (simp only [nfESize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Exchange of weakenings on spines. -/
  theorem wkSpE_wkSpE : {Γ : Ctx} → {k c a j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) c) → (sp : SpE (rem y) a j) →
      wkSpE x (wkSpE y sp) =
        wkSpE (wkv x y) (wkSpE (swp x y) (castSpE (remSwap x y).symm sp))
    | _, _, _, _, _, x, y, .nil => by
      rw [castSpE_nil]
      simp [wkSpE]
    | _, _, _, _, _, x, y, .cons sp v => by
      rw [castSpE_cons]
      simp only [wkSpE]
      rw [wkSpE_wkSpE x y sp, wkNfE_wkNfE x y v]
  termination_by _ _ _ _ _ _ _ sp => spESize sp
  decreasing_by all_goals (simp only [spESize]; omega)
end

/-- `substNfE` at the other slot of an exchange pair: the head misses, and
    the surviving position is `swp x y`. -/
theorem substNfE_ne_wkv' (x : Var Γ k) (y : Var (rem x) b) (sp : SpE Γ k .star)
    (W : NfE (rem (wkv x y)) b) :
    substNfE (.ne x sp) (wkv x y) W = .ne (swp x y) (substSpE sp (wkv x y) W) := by
  rw [show (NfE.ne x sp : NfE Γ .star) = .ne (wkv (wkv x y) (swp x y)) sp from by
    rw [wkv_swp]]
  exact substNfE_ne_wkv (wkv x y) (swp x y) sp W

/-! ## Weakening / substitution exchange -/

mutual
  /-- Weakening exchanges with hereditary substitution: substituting the
      other slot of an exchange pair into a weakened η-long form. -/
  theorem substNfE_wkNfE : {Γ : Ctx} → {k b j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) b) → (s : NfE (rem x) j) → (v : NfE (rem y) b) →
      (W : NfE (rem (wkv x y)) b) →
      W = wkNfE (swp x y) (castNfE (remSwap x y).symm v) →
      substNfE (wkNfE x s) (wkv x y) W
        = wkNfE (swp x y) (castNfE (remSwap x y).symm (substNfE s y v))
    | _, _, _, _, x, y, .lam (k₁ := k₁) s₀, v, W, hW => by
      subst hW
      have h1 := substNfE_wkNfE (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y) s₀
        (wkNfE (Var.vz (k := k₁) (Γ := rem y)) v)
        (wkNfE (.vz (k := k₁) (Γ := rem (wkv x y)))
          (wkNfE (swp x y) (castNfE (remSwap x y).symm v)))
        ((wkNfE_wkNfE (Var.vz (k := k₁) (Γ := rem (wkv x y))) (swp x y)
            (castNfE (remSwap x y).symm v)).trans
          (congrArg (wkNfE (swp (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)))
            (castNfE_wkNfE_vz (remSwap x y).symm
              (remSwap (Var.vs (k' := k₁) x)
                (Var.vs (k' := k₁) y)).symm v)).symm)
      simp only [wkNfE, substNfE]
      rw [castNfE_lam]
      simp only [wkNfE]
      exact congrArg NfE.lam h1
    | _, _, _, _, x, y, .base n, v, W, hW => by
      subst hW
      simp only [wkNfE, substNfE]
      rw [castNfE_base]
      simp [wkNfE]
    | _, _, _, _, x, y, .arrow a₀ b₀, v, W, hW => by
      subst hW
      simp only [wkNfE, substNfE]
      rw [castNfE_arrow]
      simp only [wkNfE]
      rw [substNfE_wkNfE x y a₀ v _ rfl, substNfE_wkNfE x y b₀ v _ rfl]
    | _, _, _, _, x, y, .ne (k := c) z sp, v, W, hW =>
      match c, z, sp, eqv y z with
      | _, _, sp, .same => by
        subst hW
        simp only [wkNfE]
        rw [substNfE_ne_self, substNfE_ne_self,
          substSpE_wkSpE x y sp v _ rfl,
          ← wkNfE_appSpE (swp x y) (castNfE (remSwap x y).symm v)
            (castSpE (remSwap x y).symm (substSpE sp y v)),
          ← castNfE_appSpE (remSwap x y).symm v (substSpE sp y v)]
      | _, _, sp, .diff _ z' => by
        subst hW
        simp only [wkNfE]
        rw [wkv_wkv x y z', substNfE_ne_wkv, substNfE_ne_wkv,
          castNfE_ne (remSwap x y).symm z' (substSpE sp y v)]
        simp only [wkNfE]
        rw [substSpE_wkSpE x y sp v _ rfl]
  termination_by _ _ b _ _ _ s _ _ _ => (kindSize b, 1, nfESize s)
  decreasing_by
    all_goals simp only [nfESize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right;
         first | omega | exact Nat.lt_succ_self _)
      | (apply Prod.Lex.right; apply Prod.Lex.left; omega)

  /-- Spine form of `substNfE_wkNfE`. -/
  theorem substSpE_wkSpE : {Γ : Ctx} → {k b a j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) b) → (sp : SpE (rem x) a j) → (v : NfE (rem y) b) →
      (W : NfE (rem (wkv x y)) b) →
      W = wkNfE (swp x y) (castNfE (remSwap x y).symm v) →
      substSpE (wkSpE x sp) (wkv x y) W
        = wkSpE (swp x y) (castSpE (remSwap x y).symm (substSpE sp y v))
    | _, _, _, _, _, x, y, .nil, v, W, hW => by
      subst hW
      simp only [wkSpE, substSpE]
      rw [castSpE_nil]
      simp [wkSpE]
    | _, _, _, _, _, x, y, .cons sp₀ v₀, v, W, hW => by
      subst hW
      simp only [wkSpE, substSpE]
      rw [castSpE_cons]
      simp only [wkSpE]
      rw [substSpE_wkSpE x y sp₀ v _ rfl, substNfE_wkNfE x y v₀ v _ rfl]
  termination_by _ _ b _ _ _ _ sp _ _ _ => (kindSize b, 1, spESize sp)
  decreasing_by
    all_goals simp only [spESize]
    all_goals (apply Prod.Lex.right; apply Prod.Lex.right; omega)

  /-- Weakening distributes over the spine fold. -/
  theorem wkNfE_appSpE : {Γ : Ctx} → {cw aH j : Kind} → (w : Var Γ cw) →
      (F : NfE (rem w) aH) → (SP : SpE (rem w) aH j) →
      wkNfE w (appSpE F SP) = appSpE (wkNfE w F) (wkSpE w SP)
    | _, _, _, _, w, F, .nil => by simp [wkSpE, appSpE]
    | _, _, _, _, w, F, .cons (b := bT) SP v => by
      rw [appSpE_cons]
      simp only [wkSpE]
      rw [appSpE_cons, ← wkNfE_appSpE w F SP]
      cases appSpE F SP with
      | lam T =>
        simp only [nappE, wkNfE]
        exact (substNfE_wkNfE (Var.vs (k' := bT) w) .vz T v (wkNfE w v) rfl).symm
  termination_by _ _ aH _ _ _ SP => (kindSize aH, 0, spESize SP)
  decreasing_by
    all_goals simp only [spESize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left
         have h := spEKindLe SP
         simp only [kindSize] at h ⊢
         omega)
end

/-- Weakening distributes over `nappE`. -/
theorem wkNfE_nappE : {Γ : Ctx} → {cw a b : Kind} → (w : Var Γ cw) →
    (F : NfE (rem w) (.arr a b)) → (A : NfE (rem w) a) →
    wkNfE w (nappE F A) = nappE (wkNfE w F) (wkNfE w A)
  | _, _, a, _, w, .lam T, A => by
    simp only [nappE, wkNfE]
    exact (substNfE_wkNfE (Var.vs (k' := a) w) .vz T A (wkNfE w A) rfl).symm

/-- The `vz`-instance of the exchange: substituting past a fresh top slot.
    Both casts are diagonal (`remSwap .vz y` relates `rem y` to itself), so
    the statement is cast-free. -/
theorem substNfE_wkNfE_vz {Γ : Ctx} {c k j : Kind} (X : Var Γ k) (s : NfE Γ j)
    (u : NfE (rem X) k) :
    substNfE (wkNfE (.vz (k := c) (Γ := Γ)) s) (.vs X)
        (wkNfE (.vz (k := c) (Γ := rem X)) u)
      = wkNfE (.vz (k := c) (Γ := rem X)) (substNfE s X u) :=
  substNfE_wkNfE (.vz (k := c) (Γ := Γ)) X s u
    (wkNfE (.vz (k := c) (Γ := rem X)) u) rfl

/-- Spine form of `substNfE_wkNfE_vz`. -/
theorem substSpE_wkSpE_vz {Γ : Ctx} {c k a j : Kind} (X : Var Γ k) (sp : SpE Γ a j)
    (u : NfE (rem X) k) :
    substSpE (wkSpE (.vz (k := c) (Γ := Γ)) sp) (.vs X)
        (wkNfE (.vz (k := c) (Γ := rem X)) u)
      = wkSpE (.vz (k := c) (Γ := rem X)) (substSpE sp X u) :=
  substSpE_wkSpE (.vz (k := c) (Γ := Γ)) X sp u
    (wkNfE (.vz (k := c) (Γ := rem X)) u) rfl

/-- The `vz`-instance of the weakening exchange: pulling a fresh top slot
    out past an arbitrary weakening. Both casts are diagonal. -/
theorem wkNfE_wkNfE_vz {Γ : Ctx} {c k j : Kind} (w : Var Γ k) (t : NfE (rem w) j) :
    wkNfE (.vs (k' := c) w) (wkNfE (.vz (k := c) (Γ := rem w)) t)
      = wkNfE (.vz (k := c) (Γ := Γ)) (wkNfE w t) :=
  wkNfE_wkNfE (.vs (k' := c) w) .vz t

/-- Spine form of `wkNfE_wkNfE_vz`. -/
theorem wkSpE_wkSpE_vz {Γ : Ctx} {c k a j : Kind} (w : Var Γ k) (sp : SpE (rem w) a j) :
    wkSpE (.vs (k' := c) w) (wkSpE (.vz (k := c) (Γ := rem w)) sp)
      = wkSpE (.vz (k := c) (Γ := Γ)) (wkSpE w sp) :=
  wkSpE_wkSpE (.vs (k' := c) w) .vz sp

end Systemet.L1
