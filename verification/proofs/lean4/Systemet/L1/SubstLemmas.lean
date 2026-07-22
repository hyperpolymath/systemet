-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.Conversion
/-!
# L1 substitution-commutation toolkit (ET-2, milestone 2 of MECH-1)

Keller–Altenkirch's commutation-lemma base, ported. Variable-level
computation laws for `eqv`/`wkv`, the exchange coordinates `swp`/`remSwap`,
the spine-application unrolling `appSp_cons`, commutation of the embeddings
with weakening, and the cancellation law `substNf (wkNf x t) x u = t`.
These feed both directions of `defEq_iff_nf`: soundness
(`Systemet.L1.Soundness`) and completeness (`Systemet.L1.Completeness`).

Matches on arguments whose type mentions `rem x` are pushed into term-level
`match`es after `x`'s constructor is known (the Syntax.lean idiom). Where a
`.vs`/`.vz` is written in a term whose `rem` index must reduce during
elaboration, the slot kind and context are pinned explicitly
(`Var.vs (k' := c) x`) — matcher reduction is blocked by metavariables. -/

namespace Systemet.L1

/-! ## Variable-level computation laws -/

/-- `eqv` at the diagonal computes to `same`. -/
theorem eqv_refl : {Γ : Ctx} → {k : Kind} → (x : Var Γ k) → eqv x x = .same
  | _ :: _, _, .vz => rfl
  | _ :: _, _, .vs x => by simp [eqv, eqv_refl x]

/-- `eqv` against a variable weakened past the slot computes to `diff`:
    substitution misses a variable that avoids the substituted slot. -/
theorem eqv_wkv : {Γ : Ctx} → {k j : Kind} → (x : Var Γ k) → (y : Var (rem x) j) →
    eqv x (wkv x y) = .diff x y
  | _ :: _, _, _, .vz => fun _ => rfl
  | c :: _, _, _, .vs x => fun y =>
    match y with
    | .vz => rfl
    | .vs y => by
      show eqv (Var.vs (k' := c) x) (Var.vs (wkv x y)) = _
      simp [eqv, eqv_wkv x y]

/-- `wkv x` skips `x`'s slot, so it never produces `x` itself. -/
theorem wkv_ne : {Γ : Ctx} → {k : Kind} → (x : Var Γ k) → (y : Var (rem x) k) →
    wkv x y ≠ x
  | _ :: _, _, .vz => fun _ h => by injection h
  | _ :: _, _, .vs x => fun y h => by
    cases y with
    | vz => injection h
    | vs y => exact wkv_ne x y (by injection h)

/-- `wkv x` is injective. -/
theorem wkv_inj : {Γ : Ctx} → {k j : Kind} → (x : Var Γ k) →
    (y z : Var (rem x) j) → wkv x y = wkv x z → y = z
  | _ :: _, _, _, .vz => fun _ _ h => by injection h
  | _ :: _, _, _, .vs x => fun y z =>
    match y, z with
    | .vz, .vz => fun _ => rfl
    | .vz, .vs _ => fun h => by injection h
    | .vs _, .vz => fun h => by injection h
    | .vs y, .vs z => fun h => by
      have h' : wkv x y = wkv x z := by injection h
      rw [wkv_inj x y z h']

/-! ## The exchange coordinates: `swp` and `remSwap`

Two distinct slots of `Γ` are canonically presented as a pair
`x : Var Γ k`, `y : Var (rem x) j`. Deleting them in the other order goes
through `wkv x y : Var Γ j`; `swp x y` is `x`'s position after that
deletion, and `remSwap` says both orders delete to the same context. -/

/-- `x`'s slot, as a position of `rem (wkv x y)`. -/
def swp : {Γ : Ctx} → {k j : Kind} → (x : Var Γ k) → (y : Var (rem x) j) →
    Var (rem (wkv x y)) k
  | _ :: _, _, _, .vz => fun _ => .vz
  | _ :: _, _, _, .vs x => fun y =>
    match y with
    | .vz => x
    | .vs y => .vs (swp x y)

/-- Both deletion orders reach the same context. -/
theorem remSwap : {Γ : Ctx} → {k j : Kind} → (x : Var Γ k) → (y : Var (rem x) j) →
    rem (swp x y) = rem y
  | _ :: _, _, _, .vz => fun _ => rfl
  | c :: _, _, _, .vs x => fun y =>
    match y with
    | .vz => rfl
    | .vs y => congrArg (c :: ·) (remSwap x y)

/-- Weakening `x` back past the other slot recovers `x`. -/
theorem wkv_swp : {Γ : Ctx} → {k j : Kind} → (x : Var Γ k) → (y : Var (rem x) j) →
    wkv (wkv x y) (swp x y) = x
  | _ :: _, _, _, .vz => fun _ => rfl
  | c :: _, _, _, .vs x => fun y =>
    match y with
    | .vz => rfl
    | .vs y => by
      show Var.vs (wkv (wkv x y) (swp x y)) = Var.vs (k' := c) x
      rw [wkv_swp x y]

/-! ## Spine application unrolling -/

/-- `appSp` peels its last argument through `napp`. -/
theorem appSp_cons (u : Nf Γ a) (sp : Sp Γ a (.arr b c)) (v : Nf Γ b) :
    appSp u (.cons sp v) = napp (appSp u sp) v := by
  cases h : appSp u sp with
  | lam t => simp [appSp, napp, h]
  | ne y sp' => simp [appSp, napp, h]

/-- `substNf` at the substituted head: hand off to the spine fold. -/
theorem substNf_ne_self (x : Var Γ k) (sp : Sp Γ k j) (u : Nf (rem x) k) :
    substNf (.ne x sp) x u = appSp u (substSp sp x u) := by
  simp [substNf, eqv_refl]

/-- `substNf` at a missed head: keep the neutral. -/
theorem substNf_ne_wkv (x : Var Γ k) (y : Var (rem x) c) (sp : Sp Γ c j)
    (u : Nf (rem x) k) :
    substNf (.ne (wkv x y) sp) x u = .ne y (substSp sp x u) := by
  simp [substNf, eqv_wkv]

/-! ## Embedding commutes with weakening -/

mutual
  /-- Embedding a weakened normal form is weakening the embedding. -/
  theorem embNf_wkNf : {Γ : Ctx} → {c j : Kind} → (x : Var Γ c) → (t : Nf (rem x) j) →
      embNf (wkNf x t) = wkTy x (embNf t)
    | _, _, _, x, .lam (k₁ := k₁) b => by
      simp only [wkNf, embNf, wkTy]
      exact congrArg Ty.lam (embNf_wkNf (Var.vs (k' := k₁) x) b)
    | _, _, _, _, .base n => by simp [wkNf, embNf, wkTy]
    | _, _, _, x, .arrow a b => by
      simp [wkNf, embNf, wkTy, embNf_wkNf x a, embNf_wkNf x b]
    | _, _, _, x, .ne y sp => by
      have h := embSp_wkSp x (.var y) sp
      simp only [wkTy] at h
      simp [wkNf, embNf, h]
  termination_by _ _ _ _ t => nfSize t
  decreasing_by all_goals (simp only [nfSize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Spine form of `embNf_wkNf`. -/
  theorem embSp_wkSp : {Γ : Ctx} → {c a j : Kind} → (x : Var Γ c) → (h : Ty (rem x) a) →
      (sp : Sp (rem x) a j) → embSp (wkTy x h) (wkSp x sp) = wkTy x (embSp h sp)
    | _, _, _, _, _, _, .nil => by simp [wkSp, embSp]
    | _, _, _, _, x, h, .cons sp v => by
      simp [wkSp, embSp, wkTy, embSp_wkSp x h sp, embNf_wkNf x v]
  termination_by _ _ _ _ _ _ sp => spSize sp
  decreasing_by all_goals (simp only [spSize]; omega)
end

/-! ## Cancellation: substituting a freshly weakened term -/

mutual
  /-- Substituting at a slot the term was just weakened past is the identity. -/
  theorem substNf_wkNf_cancel : {Γ : Ctx} → {k j : Kind} → (x : Var Γ k) →
      (t : Nf (rem x) j) → (u : Nf (rem x) k) → substNf (wkNf x t) x u = t
    | _, _, _, x, .lam (k₁ := k₁) b, u => by
      simp only [wkNf, substNf]
      exact congrArg Nf.lam
        (substNf_wkNf_cancel (Var.vs (k' := k₁) x) b (wkNf .vz u))
    | _, _, _, _, .base n, _ => by simp [wkNf, substNf]
    | _, _, _, x, .arrow a b, u => by
      simp [wkNf, substNf, substNf_wkNf_cancel x a u, substNf_wkNf_cancel x b u]
    | _, _, _, x, .ne y sp, u => by
      simp [wkNf, substNf_ne_wkv, substSp_wkSp_cancel x sp u]
  termination_by _ _ _ _ t _ => nfSize t
  decreasing_by all_goals (simp only [nfSize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Spine form of `substNf_wkNf_cancel`. -/
  theorem substSp_wkSp_cancel : {Γ : Ctx} → {k a j : Kind} → (x : Var Γ k) →
      (sp : Sp (rem x) a j) → (u : Nf (rem x) k) → substSp (wkSp x sp) x u = sp
    | _, _, _, _, _, .nil, _ => by simp [wkSp, substSp]
    | _, _, _, _, x, .cons sp v, u => by
      simp [wkSp, substSp, substSp_wkSp_cancel x sp u, substNf_wkNf_cancel x v u]
  termination_by _ _ _ _ _ sp _ => spSize sp
  decreasing_by all_goals (simp only [spSize]; omega)
end

/-! ## Context-cast toolkit

The exchange laws relate removals performed in both orders; `remSwap`
equates the resulting contexts propositionally, so terms are carried
across by `Eq.rec`. Lean's definitional proof irrelevance makes every
diagonal cast vanish (`castNf_diag` is `rfl`), so instances of the
exchange laws whose contexts agree definitionally are cast-free. -/

/-- Transport a variable along a context equality. -/
def castV (h : Δ = Δ') (v : Var Δ j) : Var Δ' j := h ▸ v

/-- Transport a normal form along a context equality. -/
def castNf (h : Δ = Δ') (t : Nf Δ j) : Nf Δ' j := h ▸ t

/-- Transport a spine along a context equality. -/
def castSp (h : Δ = Δ') (s : Sp Δ a j) : Sp Δ' a j := h ▸ s

theorem castV_diag (e : Δ = Δ) (v : Var Δ j) : castV e v = v := rfl

theorem castNf_diag (e : Δ = Δ) (t : Nf Δ j) : castNf e t = t := rfl

theorem castSp_diag (e : Δ = Δ) (s : Sp Δ a j) : castSp e s = s := rfl

theorem castV_vz (e : (c :: Δ : Ctx) = c :: Δ') :
    castV e (.vz (k := c) (Γ := Δ)) = .vz := by
  have h : Δ = Δ' := by injection e
  subst h; rfl

theorem castV_vs (e : (c :: Δ : Ctx) = c :: Δ') (h : Δ = Δ') (v : Var Δ j) :
    castV e (.vs v) = .vs (castV h v) := by
  subst h; rfl

theorem castNf_lam (h : Δ = Δ') (b : Nf (k₁ :: Δ) k₂) :
    castNf h (.lam b) = .lam (castNf (congrArg (k₁ :: ·) h) b) := by
  subst h; rfl

theorem castNf_base (h : Δ = Δ') (n : Nat) :
    castNf h (.base n) = .base n := by
  subst h; rfl

theorem castNf_arrow (h : Δ = Δ') (a b : Nf Δ .star) :
    castNf h (.arrow a b) = .arrow (castNf h a) (castNf h b) := by
  subst h; rfl

theorem castNf_ne (h : Δ = Δ') (y : Var Δ c) (sp : Sp Δ c j) :
    castNf h (.ne y sp) = .ne (castV h y) (castSp h sp) := by
  subst h; rfl

theorem castSp_nil (h : Δ = Δ') :
    castSp h (.nil (Γ := Δ) (k := a)) = .nil := by
  subst h; rfl

theorem castSp_cons (h : Δ = Δ') (sp : Sp Δ a (.arr b c)) (v : Nf Δ b) :
    castSp h (.cons sp v) = .cons (castSp h sp) (castNf h v) := by
  subst h; rfl

theorem castNf_appSp (h : Δ = Δ') (F : Nf Δ a) (SP : Sp Δ a j) :
    castNf h (appSp F SP) = appSp (castNf h F) (castSp h SP) := by
  subst h; rfl

theorem castNf_castNf (e : Δ = Δ') (e' : Δ' = Δ'') (t : Nf Δ j) :
    castNf e' (castNf e t) = castNf (e.trans e') t := by
  subst e; subst e'; rfl

/-- Transporting past a fresh top slot commutes with weakening at `vz`. -/
theorem castNf_wkNf_vz (h : Δ = Δ') (e : (c :: Δ : Ctx) = c :: Δ') (t : Nf Δ j) :
    castNf e (wkNf (.vz (k := c) (Γ := Δ)) t) = wkNf .vz (castNf h t) := by
  subst h; rfl

/-- Spine form of `castNf_wkNf_vz`. -/
theorem castSp_wkSp_vz (h : Δ = Δ') (e : (c :: Δ : Ctx) = c :: Δ') (sp : Sp Δ a j) :
    castSp e (wkSp (.vz (k := c) (Γ := Δ)) sp) = wkSp .vz (castSp h sp) := by
  subst h; rfl

/-! ## Exchange of weakenings -/

/-- Variable-level exchange of weakenings. -/
theorem wkv_wkv : {Γ : Ctx} → {k c j : Kind} → (x : Var Γ k) → (y : Var (rem x) c) →
    (v : Var (rem y) j) →
    wkv x (wkv y v) = wkv (wkv x y) (wkv (swp x y) (castV (remSwap x y).symm v))
  | _ :: _, _, _, _, .vz => fun _ _ => rfl
  | c₀ :: _, _, _, _, .vs x => fun y =>
    match y with
    | .vz => fun _ => rfl
    | .vs y => fun v =>
      match v with
      | .vz => by
        have h : castV (remSwap (Var.vs (k' := c₀) x) (Var.vs (k' := c₀) y)).symm
            (Var.vz (k := c₀) (Γ := rem y)) = Var.vz := castV_vz _
        rw [h]
        rfl
      | .vs v => by
        have h : castV (remSwap (Var.vs (k' := c₀) x) (Var.vs (k' := c₀) y)).symm
            (Var.vs (k' := c₀) v) = Var.vs (castV (remSwap x y).symm v) :=
          castV_vs _ _ v
        rw [h]
        show Var.vs (wkv x (wkv y v)) = _
        rw [wkv_wkv x y v]
        rfl

mutual
  /-- Exchange of weakenings on normal forms. -/
  theorem wkNf_wkNf : {Γ : Ctx} → {k c j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) c) → (t : Nf (rem y) j) →
      wkNf x (wkNf y t) =
        wkNf (wkv x y) (wkNf (swp x y) (castNf (remSwap x y).symm t))
    | _, _, _, _, x, y, .lam (k₁ := k₁) b => by
      rw [castNf_lam]
      simp only [wkNf]
      exact congrArg Nf.lam
        (wkNf_wkNf (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y) b)
    | _, _, _, _, x, y, .base n => by
      rw [castNf_base]
      simp [wkNf]
    | _, _, _, _, x, y, .arrow a b => by
      rw [castNf_arrow]
      simp only [wkNf]
      rw [wkNf_wkNf x y a, wkNf_wkNf x y b]
    | _, _, _, _, x, y, .ne z sp => by
      rw [castNf_ne]
      simp only [wkNf]
      rw [wkv_wkv x y z, wkSp_wkSp x y sp]
  termination_by _ _ _ _ _ _ t => nfSize t
  decreasing_by all_goals (simp only [nfSize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Exchange of weakenings on spines. -/
  theorem wkSp_wkSp : {Γ : Ctx} → {k c a j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) c) → (sp : Sp (rem y) a j) →
      wkSp x (wkSp y sp) =
        wkSp (wkv x y) (wkSp (swp x y) (castSp (remSwap x y).symm sp))
    | _, _, _, _, _, x, y, .nil => by
      rw [castSp_nil]
      simp [wkSp]
    | _, _, _, _, _, x, y, .cons sp v => by
      rw [castSp_cons]
      simp only [wkSp]
      rw [wkSp_wkSp x y sp, wkNf_wkNf x y v]
  termination_by _ _ _ _ _ _ _ sp => spSize sp
  decreasing_by all_goals (simp only [spSize]; omega)
end

/-- `substNf` at the other slot of an exchange pair: the head misses, and
    the surviving position is `swp x y`. -/
theorem substNf_ne_wkv' (x : Var Γ k) (y : Var (rem x) b) (sp : Sp Γ k j)
    (W : Nf (rem (wkv x y)) b) :
    substNf (.ne x sp) (wkv x y) W = .ne (swp x y) (substSp sp (wkv x y) W) := by
  rw [show (Nf.ne x sp : Nf Γ j) = .ne (wkv (wkv x y) (swp x y)) sp from by
    rw [wkv_swp]]
  exact substNf_ne_wkv (wkv x y) (swp x y) sp W

/-! ## Weakening / substitution exchange -/

mutual
  /-- Weakening exchanges with hereditary substitution: substituting the
      other slot of an exchange pair into a weakened normal form. -/
  theorem substNf_wkNf : {Γ : Ctx} → {k b j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) b) → (s : Nf (rem x) j) → (v : Nf (rem y) b) →
      (W : Nf (rem (wkv x y)) b) →
      W = wkNf (swp x y) (castNf (remSwap x y).symm v) →
      substNf (wkNf x s) (wkv x y) W
        = wkNf (swp x y) (castNf (remSwap x y).symm (substNf s y v))
    | _, _, _, _, x, y, .lam (k₁ := k₁) s₀, v, W, hW => by
      subst hW
      have h1 := substNf_wkNf (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y) s₀
        (wkNf (Var.vz (k := k₁) (Γ := rem y)) v)
        (wkNf (.vz (k := k₁) (Γ := rem (wkv x y)))
          (wkNf (swp x y) (castNf (remSwap x y).symm v)))
        ((wkNf_wkNf (Var.vz (k := k₁) (Γ := rem (wkv x y))) (swp x y)
            (castNf (remSwap x y).symm v)).trans
          (congrArg (wkNf (swp (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)))
            (castNf_wkNf_vz (remSwap x y).symm
              (remSwap (Var.vs (k' := k₁) x)
                (Var.vs (k' := k₁) y)).symm v)).symm)
      simp only [wkNf, substNf]
      rw [castNf_lam]
      simp only [wkNf]
      exact congrArg Nf.lam h1
    | _, _, _, _, x, y, .base n, v, W, hW => by
      subst hW
      simp only [wkNf, substNf]
      rw [castNf_base]
      simp [wkNf]
    | _, _, _, _, x, y, .arrow a₀ b₀, v, W, hW => by
      subst hW
      simp only [wkNf, substNf]
      rw [castNf_arrow]
      simp only [wkNf]
      rw [substNf_wkNf x y a₀ v _ rfl, substNf_wkNf x y b₀ v _ rfl]
    | _, _, _, _, x, y, .ne (k := c) z sp, v, W, hW =>
      match c, z, sp, eqv y z with
      | _, _, sp, .same => by
        subst hW
        simp only [wkNf]
        rw [substNf_ne_self, substNf_ne_self,
          substSp_wkSp x y sp v _ rfl,
          ← wkNf_appSp (swp x y) (castNf (remSwap x y).symm v)
            (castSp (remSwap x y).symm (substSp sp y v)),
          ← castNf_appSp (remSwap x y).symm v (substSp sp y v)]
      | _, _, sp, .diff _ z' => by
        subst hW
        simp only [wkNf]
        rw [wkv_wkv x y z', substNf_ne_wkv, substNf_ne_wkv,
          castNf_ne (remSwap x y).symm z' (substSp sp y v)]
        simp only [wkNf]
        rw [substSp_wkSp x y sp v _ rfl]
  termination_by _ _ b _ _ _ s _ _ _ => (kindSize b, 1, nfSize s)
  decreasing_by
    all_goals simp only [nfSize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right;
         first | omega | exact Nat.lt_succ_self _)
      | (apply Prod.Lex.right; apply Prod.Lex.left; omega)

  /-- Spine form of `substNf_wkNf`. -/
  theorem substSp_wkSp : {Γ : Ctx} → {k b a j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) b) → (sp : Sp (rem x) a j) → (v : Nf (rem y) b) →
      (W : Nf (rem (wkv x y)) b) →
      W = wkNf (swp x y) (castNf (remSwap x y).symm v) →
      substSp (wkSp x sp) (wkv x y) W
        = wkSp (swp x y) (castSp (remSwap x y).symm (substSp sp y v))
    | _, _, _, _, _, x, y, .nil, v, W, hW => by
      subst hW
      simp only [wkSp, substSp]
      rw [castSp_nil]
      simp [wkSp]
    | _, _, _, _, _, x, y, .cons sp₀ v₀, v, W, hW => by
      subst hW
      simp only [wkSp, substSp]
      rw [castSp_cons]
      simp only [wkSp]
      rw [substSp_wkSp x y sp₀ v _ rfl, substNf_wkNf x y v₀ v _ rfl]
  termination_by _ _ b _ _ _ _ sp _ _ _ => (kindSize b, 1, spSize sp)
  decreasing_by
    all_goals simp only [spSize]
    all_goals (apply Prod.Lex.right; apply Prod.Lex.right; omega)

  /-- Weakening distributes over the spine fold. -/
  theorem wkNf_appSp : {Γ : Ctx} → {cw aH j : Kind} → (w : Var Γ cw) →
      (F : Nf (rem w) aH) → (SP : Sp (rem w) aH j) →
      wkNf w (appSp F SP) = appSp (wkNf w F) (wkSp w SP)
    | _, _, _, _, w, F, .nil => by simp [wkSp, appSp]
    | _, _, _, _, w, F, .cons (b := bT) SP v => by
      rw [appSp_cons]
      simp only [wkSp]
      rw [appSp_cons, ← wkNf_appSp w F SP]
      cases appSp F SP with
      | lam T =>
        simp only [napp, wkNf]
        exact (substNf_wkNf (Var.vs (k' := bT) w) .vz T v (wkNf w v) rfl).symm
      | ne yh sph =>
        simp [napp, wkNf, wkSp]
  termination_by _ _ aH _ _ _ SP => (kindSize aH, 0, spSize SP)
  decreasing_by
    all_goals simp only [spSize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left
         have h := spKindLe SP
         simp only [kindSize] at h ⊢
         omega)
end

/-- Weakening distributes over `napp`. -/
theorem wkNf_napp : {Γ : Ctx} → {cw a b : Kind} → (w : Var Γ cw) →
    (F : Nf (rem w) (.arr a b)) → (A : Nf (rem w) a) →
    wkNf w (napp F A) = napp (wkNf w F) (wkNf w A)
  | _, _, a, _, w, .lam T, A => by
    simp only [napp, wkNf]
    exact (substNf_wkNf (Var.vs (k' := a) w) .vz T A (wkNf w A) rfl).symm
  | _, _, _, _, w, .ne y sp, A => by
    simp [napp, wkNf, wkSp]

/-- Normalization commutes with weakening. -/
theorem nf_wkTy : {Γ : Ctx} → {c j : Kind} → (x : Var Γ c) → (t : Ty (rem x) j) →
    nf (wkTy x t) = wkNf x (nf t)
  | _, _, _, x, .var y => by simp [wkTy, nf, wkNf, wkSp]
  | _, _, _, x, .base n => by simp [wkTy, nf, wkNf]
  | _, _, _, x, .arrow a b => by simp [wkTy, nf, wkNf, nf_wkTy x a, nf_wkTy x b]
  | _, _, _, x, .lam (k₁ := k₁) b => by
    simp only [wkTy, nf, wkNf]
    exact congrArg Nf.lam (nf_wkTy (Var.vs (k' := k₁) x) b)
  | _, _, _, x, .app f a => by
    simp only [wkTy, nf]
    rw [nf_wkTy x f, nf_wkTy x a, wkNf_napp]
termination_by _ _ _ _ t => tySize t
decreasing_by all_goals (simp only [tySize]; first | exact Nat.lt_succ_self _ | omega)


theorem castV_symm_cancel (e : Δ = Δ') (v : Var Δ' j) :
    castV e (castV e.symm v) = v := by
  subst e; rfl

theorem castNf_symm_cancel (e : Δ = Δ') (t : Nf Δ' j) :
    castNf e (castNf e.symm t) = t := by
  subst e; rfl

theorem castSp_symm_cancel (e : Δ = Δ') (sp : Sp Δ' a j) :
    castSp e (castSp e.symm sp) = sp := by
  subst e; rfl

/-! ## Lexicographic-descent helpers

`apply Prod.Lex.right` unifies first components syntactically, which fails
when they are equal only up to arithmetic (the sum measure below). These
intros take the comparisons as arithmetic side goals instead. -/

theorem lex3_lt {a₁ a₂ b₁ b₂ c₁ c₂ : Nat} (h : a₁ < a₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a₁, b₁, c₁) (a₂, b₂, c₂) :=
  Prod.Lex.left _ _ h

theorem lex3_eq_lt {a₁ a₂ b₁ b₂ c₁ c₂ : Nat} (h : a₁ = a₂) (hb : b₁ < b₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a₁, b₁, c₁) (a₂, b₂, c₂) := by
  subst h; exact Prod.Lex.right _ (Prod.Lex.left _ _ hb)

theorem lex3_eq_eq_lt {a₁ a₂ b₁ b₂ c₁ c₂ : Nat} (h : a₁ = a₂) (hb : b₁ = b₂)
    (hc : c₁ < c₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a₁, b₁, c₁) (a₂, b₂, c₂) := by
  subst h; subst hb; exact Prod.Lex.right _ (Prod.Lex.right _ hc)

/-! ## Exchange of substitutions (the substitution lemma) -/

mutual
  /-- Exchange of hereditary substitutions: the substitution lemma. -/
  theorem substNf_substNf : {Γ : Ctx} → {k b j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) b) → (t : Nf Γ j) → (u : Nf (rem x) k) →
      (a : Nf (rem y) b) → (W : Nf (rem (wkv x y)) b) →
      W = wkNf (swp x y) (castNf (remSwap x y).symm a) →
      substNf (substNf t x u) y a
        = castNf (remSwap x y)
            (substNf (substNf t (wkv x y) W) (swp x y)
              (castNf (remSwap x y).symm (substNf u y a)))
    | _, _, _, _, x, y, .lam (k₁ := k₁) t₀, u, a, W, hW => by
      subst hW
      have hγ : castNf (remSwap (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)).symm
          (substNf (wkNf (Var.vz (k := k₁) (Γ := rem x)) u) (Var.vs (k' := k₁) y)
            (wkNf (Var.vz (k := k₁) (Γ := rem y)) a))
          = wkNf (Var.vz (k := k₁) (Γ := rem (swp x y)))
              (castNf (remSwap x y).symm (substNf u y a)) :=
        (congrArg
            (castNf (remSwap (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)).symm)
            (substNf_wkNf (Var.vz (k := k₁) (Γ := rem x)) y u a
              (wkNf (Var.vz (k := k₁) (Γ := rem y)) a) rfl)).trans
          (castNf_wkNf_vz (remSwap x y).symm
            (remSwap (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)).symm
            (substNf u y a))
      have h1 := substNf_substNf (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y) t₀
        (wkNf (Var.vz (k := k₁) (Γ := rem x)) u)
        (wkNf (Var.vz (k := k₁) (Γ := rem y)) a)
        (wkNf (Var.vz (k := k₁) (Γ := rem (wkv x y)))
          (wkNf (swp x y) (castNf (remSwap x y).symm a)))
        ((wkNf_wkNf (Var.vz (k := k₁) (Γ := rem (wkv x y))) (swp x y)
            (castNf (remSwap x y).symm a)).trans
          (congrArg (wkNf (swp (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)))
            (castNf_wkNf_vz (remSwap x y).symm
              (remSwap (Var.vs (k' := k₁) x)
                (Var.vs (k' := k₁) y)).symm a)).symm)
      simp only [substNf]
      rw [castNf_lam]
      exact congrArg Nf.lam (h1.trans (congrArg
        (castNf (remSwap (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)))
        (congrArg
          (substNf (substNf t₀ (wkv (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y))
              (wkNf (Var.vz (k := k₁) (Γ := rem (wkv x y)))
                (wkNf (swp x y) (castNf (remSwap x y).symm a))))
            (swp (Var.vs (k' := k₁) x) (Var.vs (k' := k₁) y)))
          hγ)))
    | _, _, _, _, x, y, .base n, u, a, W, hW => by
      subst hW
      simp only [substNf]
      rw [castNf_base]
    | _, _, _, _, x, y, .arrow a₀ b₀, u, a, W, hW => by
      subst hW
      simp only [substNf]
      rw [castNf_arrow]
      rw [substNf_substNf x y a₀ u a _ rfl, substNf_substNf x y b₀ u a _ rfl]
    | _, _, _, _, x, y, .ne (k := c) z sp, u, a, W, hW =>
      match c, z, sp, eqv x z with
      | _, _, sp, .same => by
        subst hW
        rw [substNf_ne_self, substNf_appSp u (substSp sp x u) y a,
          substSp_substSp x y sp u a _ rfl,
          substNf_ne_wkv', substNf_ne_self, castNf_appSp,
          castNf_symm_cancel]
      | _, _, sp, .diff _ z' =>
        match c, z', sp, eqv y z' with
        | _, _, sp, .same => by
          subst hW
          rw [substNf_ne_wkv, substNf_ne_self, substNf_ne_self,
            substSp_substSp x y sp u a _ rfl,
            substNf_appSp _ _ (swp x y) _,
            substNf_wkNf_cancel, castNf_appSp, castNf_symm_cancel]
        | _, _, sp, .diff _ z'' => by
          subst hW
          rw [substNf_ne_wkv, substNf_ne_wkv,
            substSp_substSp x y sp u a _ rfl,
            wkv_wkv x y z'', substNf_ne_wkv, substNf_ne_wkv,
            castNf_ne, castV_symm_cancel]
  termination_by _ k b _ x y t _ _ _ _ => (kindSize k + kindSize b, 1, nfSize t)
  decreasing_by
    all_goals simp only [nfSize]
    all_goals first
      | exact lex3_eq_eq_lt (by omega) rfl
          (by first | omega | exact Nat.lt_succ_self _)
      | exact lex3_eq_lt (by omega) (by omega)

  /-- Spine form of the substitution lemma. -/
  theorem substSp_substSp : {Γ : Ctx} → {k b aS j : Kind} → (x : Var Γ k) →
      (y : Var (rem x) b) → (sp : Sp Γ aS j) → (u : Nf (rem x) k) →
      (a : Nf (rem y) b) → (W : Nf (rem (wkv x y)) b) →
      W = wkNf (swp x y) (castNf (remSwap x y).symm a) →
      substSp (substSp sp x u) y a
        = castSp (remSwap x y)
            (substSp (substSp sp (wkv x y) W) (swp x y)
              (castNf (remSwap x y).symm (substNf u y a)))
    | _, _, _, _, _, x, y, .nil, u, a, W, hW => by
      subst hW
      simp only [substSp]
      rw [castSp_nil]
    | _, _, _, _, _, x, y, .cons sp₀ v₀, u, a, W, hW => by
      subst hW
      simp only [substSp]
      rw [castSp_cons]
      rw [substSp_substSp x y sp₀ u a _ rfl, substNf_substNf x y v₀ u a _ rfl]
  termination_by _ k b _ _ x y sp _ _ _ _ => (kindSize k + kindSize b, 1, spSize sp)
  decreasing_by
    all_goals simp only [spSize]
    all_goals first
      | exact lex3_eq_eq_lt (by omega) rfl
          (by first | omega | exact Nat.lt_succ_self _)
      | exact lex3_eq_lt (by omega) (by omega)

  /-- Hereditary substitution distributes over the spine fold. -/
  theorem substNf_appSp : {Δ : Ctx} → {aH kq j : Kind} → (F : Nf Δ aH) →
      (SP : Sp Δ aH j) → (q : Var Δ kq) → (w : Nf (rem q) kq) →
      substNf (appSp F SP) q w = appSp (substNf F q w) (substSp SP q w)
    | _, _, _, _, F, .nil, q, w => by simp [appSp, substSp]
    | Δ, _, _, _, F, .cons (b := bT) SP v, q, w => by
      rw [appSp_cons]
      simp only [substSp]
      rw [appSp_cons, ← substNf_appSp F SP q w]
      cases appSp F SP with
      | lam T =>
        simp only [napp, substNf]
        exact substNf_substNf (Var.vz (k := bT) (Γ := Δ)) q T v w
          (wkNf (Var.vz (k := bT) (Γ := rem q)) w) rfl
      | ne yh sph =>
        cases eqv q yh with
        | same =>
          simp only [napp]
          rw [substNf_ne_self, substNf_ne_self]
          simp only [substSp]
          rw [appSp_cons]
          rfl
        | diff _ qz =>
          simp only [napp]
          rw [substNf_ne_wkv, substNf_ne_wkv]
          simp only [substSp]
  termination_by _ aH kq _ _ SP _ _ => (kindSize aH + kindSize kq, 0, spSize SP)
  decreasing_by
    all_goals simp only [spSize]
    all_goals first
      | exact lex3_eq_eq_lt (by omega) rfl
          (by first | omega | exact Nat.lt_succ_self _)
      | exact lex3_eq_lt (by omega) (by omega)
      | exact lex3_lt (by
          have h := spKindLe SP
          simp only [kindSize] at h ⊢
          omega)
end


/-- Hereditary substitution distributes over `napp`. -/
theorem substNf_napp : {Γ : Ctx} → {a b kq : Kind} → (F : Nf Γ (.arr a b)) →
    (A : Nf Γ a) → (q : Var Γ kq) → (w : Nf (rem q) kq) →
    substNf (napp F A) q w = napp (substNf F q w) (substNf A q w)
  | Γ, a, _, _, .lam T, A, q, w => by
    simp only [napp, substNf]
    exact substNf_substNf (Var.vz (k := a) (Γ := Γ)) q T A w
      (wkNf (Var.vz (k := a) (Γ := rem q)) w) rfl
  | _, _, _, _, .ne yh sph, A, q, w => by
    cases eqv q yh with
    | same =>
      simp only [napp]
      rw [substNf_ne_self, substNf_ne_self]
      simp only [substSp]
      rw [appSp_cons]
      rfl
    | diff _ qz =>
      simp only [napp]
      rw [substNf_ne_wkv, substNf_ne_wkv]
      simp only [substSp]

/-- Normalization commutes with syntactic substitution — the main
    Keller-Altenkirch commutation equation for ET-2. -/
theorem nf_substTy : {Γ : Ctx} → {j k : Kind} → (t : Ty Γ j) → (x : Var Γ k) →
    (u : Ty (rem x) k) → nf (substTy t x u) = substNf (nf t) x (nf u)
  | _, j, _, .var z, x, u =>
    match j, z, eqv x z with
    | _, _, .same => by
      simp only [nf]
      rw [substNf_ne_self]
      simp [substTy, eqv_refl, appSp, substSp]
    | _, _, .diff _ z' => by
      simp only [nf]
      rw [substNf_ne_wkv]
      simp [substTy, eqv_wkv, substSp, nf]
  | _, _, _, .base n, x, u => by simp [substTy, nf, substNf]
  | _, _, _, .arrow a b, x, u => by
    simp only [substTy, nf, substNf]
    rw [nf_substTy a x u, nf_substTy b x u]
  | _, _, _, .lam (k₁ := k₁) b, x, u => by
    simp only [substTy, nf, substNf]
    exact congrArg Nf.lam
      ((nf_substTy b (Var.vs (k' := k₁) x)
          (wkTy (Var.vz (k := k₁) (Γ := rem x)) u)).trans
        (congrArg (substNf (nf b) (Var.vs (k' := k₁) x))
          (nf_wkTy (Var.vz (k := k₁) (Γ := rem x)) u)))
  | _, _, _, .app f a, x, u => by
    simp only [substTy, nf]
    rw [nf_substTy f x u, nf_substTy a x u, substNf_napp]
termination_by _ _ _ t _ _ => tySize t
decreasing_by all_goals (simp only [tySize]; first | exact Nat.lt_succ_self _ | omega)

end Systemet.L1
