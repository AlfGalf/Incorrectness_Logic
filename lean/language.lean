import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

namespace IncLoLang

/-! ## State-/

meta def tactic.dec_trivial := `[exact dec_trivial]

def state: Type := string -> ℕ

def state.update : string -> ℕ -> state -> state
| name val σ := (λ name', if name' = name then val else σ name')

notation s `{` name ` ↦ ` val `}` := state.update name val s

@[simp] lemma state.update_apply (name : string) (val : ℕ) (s : state) :
  s{name ↦ val} name = val :=
begin
  unfold state.update,
  finish,
end

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state)
    (h : name' ≠ name) :
  s{name ↦ val} name' = s name' :=
begin
  unfold state.update,
  exact if_neg h,
end

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma update_swap (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state)
    (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma update_id (name : string) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

@[simp] lemma update_same_const (name : string) (val : ℕ) :
  (λ_, val){name ↦ val} = (λ_, val) :=
by apply funext; simp

/-! # Propositions -/

def prop: Type := state -> Prop

/-! # Expression -/

def expression: Type := state -> ℕ

/-! ## Language -/

inductive stmt : Type
| skip            : stmt
| assign          : string → expression → stmt
| non_det_assign  : string → stmt
| seq             : stmt → stmt → stmt
| choice          : stmt → stmt → stmt
| star            : stmt → stmt
| local_var       : string → stmt → stmt
| error           : stmt
| assumes         : prop → stmt

-- Language notation

infixr ` ;; ` : 90 := stmt.seq

infixr ` <+> ` : 90 := stmt.choice

postfix `**` : 90 := stmt.star

notation `[` x ` ↣ ` e `]` := stmt.assign x e

notation `[loc` x `.` C `]` := stmt.local_var x C

/- This is the definition of P[x'/x] used in the paper -/
def p_thing (P: prop) (x': ℕ) (x: string) : IncLoLang.state -> Prop :=
  -- λ σ', ∃ σ, P σ ∧ σ' = σ{x ↦ x'}
  -- This is the definition given int he paper but it is wrong
  λ σ', P (σ'{x ↦ x'})
-- ie, True for σ if P(σ{x ↦ x'})

notation P `{` name ` ↣ ` val `}` := p_thing P val name

/-! # Language semantics -/

inductive LogicType : Type
| er
| ok

def repeat: IncLoLang.stmt → ℕ → IncLoLang.stmt 
| C nat.zero := IncLoLang.stmt.skip
| C (nat.succ i) := (repeat C (i)) ;; C

inductive lang_semantics: IncLoLang.stmt -> LogicType -> IncLoLang.state -> IncLoLang.state -> Prop
| skip {s} :
  lang_semantics IncLoLang.stmt.skip LogicType.ok s s
| seq_ty {S T s t u ty} (H1: lang_semantics S LogicType.ok s t) (H2: lang_semantics T ty t u) :
  lang_semantics(S ;; T) ty s u
| seq_er_1 {S T s t} (H1: lang_semantics S LogicType.er s t): 
  lang_semantics (S ;; T) LogicType.er s t
| error {s}:
  lang_semantics IncLoLang.stmt.error LogicType.er s s
| assign {x s e} :
  lang_semantics [x ↣ e] LogicType.ok s (s{x ↦ (e s)})
| non_det_assign {x s} (v: ℕ) :
  lang_semantics (IncLoLang.stmt.non_det_assign x) LogicType.ok s (s{x ↦ v})
| assumes_ok {s} {B: prop} (h: B s) :
  lang_semantics (IncLoLang.stmt.assumes B) LogicType.ok s s
| choice_left {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₁ ty s₁ s₂)): 
  lang_semantics (C₁ <+> C₂) ty s₁ s₂
| choice_right {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₂ ty s₁ s₂)): 
  lang_semantics (C₁ <+> C₂) ty s₁ s₂
| star {C s₁ s₂ ty} (i: ℕ) (h: lang_semantics (repeat C i) ty s₁ s₂):
  lang_semantics (C**) ty s₁ s₂
| local_var {C s₁ s₂ ty x v} (h: lang_semantics C ty s₁ s₂):
  lang_semantics ([loc x . C]) ty (s₁{x ↦ v}) (s₂{x ↦ v})

/-! # Free-/

-- Perhaps invert
def prop.Free (P: prop): set string :=
  λ x, ∃ σ v, (P σ ∧ ¬(P (σ{x ↦ v})))

-- def stmt.Free (C: stmt): set string := // old definition
--   λ x, ∀ σ σ' ty v, lang_semantics C ty σ σ' → lang_semantics C ty (σ{x ↦ v}) (σ'{x ↦ v})

def expression.Free (e: expression): set string := 
  λ x, ∃ σ v, e σ ≠ e (σ{x ↦ v})

def stmt.Free: stmt → set string 
| stmt.skip                 := {}
| ([z ↣ e₂])                := {z} ∪ e₂.Free
| (stmt.non_det_assign z)   := {z}
| (C₁ ;; C₂)                := (stmt.Free C₁) ∪ (stmt.Free C₂)
| (C₁ <+> C₂)               := (stmt.Free C₁) ∪ (stmt.Free C₂)
| (C**)                     := stmt.Free C
| [loc z . C]               := (stmt.Free C) \ {z}
| stmt.error                := {}
| (stmt.assumes P)          := prop.Free P

/-! # Substitute-/

def state.substitute : string → string → state → state
| x y := λ σ, σ{y ↦ σ x}
-- | x y := λ σ, σ{y ↦ σ x}{x ↦ 0}

notation σ `⟨` vto `//` vfrom `⟩` :=  state.substitute vto vfrom σ

def prop.substitute : string → string → prop → prop
| x s P := λ σ, P (σ{x ↦ σ s})

notation P `[` val `//` name `]` :=  prop.substitute name val P

def expression.substitute : string → string → expression → expression
| x y e := λ σ, e (σ⟨ y // x ⟩)

def stmt.substitute : string → string → stmt → stmt
| x y stmt.skip                 := stmt.skip
| x y ([z ↣ e₂])                := if x = z then [y ↣ λ σ, ((expression.substitute x y e₂) σ)] else [z ↣ λ σ, ((expression.substitute x y e₂) σ)]  -- PUT X BACK!
| x y (stmt.non_det_assign s)   := stmt.non_det_assign s
| x y (C₁ ;; C₂)                := (stmt.substitute x y C₁) ;; (stmt.substitute x y C₂)
| x y (C₁ <+> C₂)               := (stmt.substitute x y C₁) <+> (stmt.substitute x y C₂)
| x y (C**)                     := (stmt.substitute x y C)**
| x y [loc z . C]               := if x = z then [loc x . C] else [loc z . (stmt.substitute x y C)]
| x y stmt.error                := stmt.error
| x y (stmt.assumes P)          := stmt.assumes (P[y//x])

notation C `{` exp `//` name `}` :=  stmt.substitute name exp C

/-! ## Mod -/

def Mod: stmt -> set string
| (C₁ ;; C₂) := (Mod C₁) ∪ (Mod C₂)
| (C₁ <+> C₂) := (Mod C₁) ∪ (Mod C₂)
| (C**) := (Mod C)
| ([x ↣ v]) := {x}
| (IncLoLang.stmt.skip) := {}
| (IncLoLang.stmt.non_det_assign x) := {x}
| (IncLoLang.stmt.assumes _) := {}
| (IncLoLang.stmt.error) := {}
| (IncLoLang.stmt.local_var x C) := Mod C \ {x}

lemma mod_elem_left_elem_seq (C₁ C₂: stmt):
   Mod C₁ ⊆ Mod (C₁ ;; C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma mod_elem_right_elem_seq (C₁ C₂: stmt):
   Mod C₂ ⊆ Mod (C₁ ;; C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma mod_elem_left_elem_choice (C₁ C₂: stmt):
   Mod C₁ ⊆ Mod (C₁ <+> C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma mod_elem_right_elem_choice (C₁ C₂: stmt):
   Mod C₂ ⊆ Mod (C₁ <+> C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma start_seq {C: stmt} {σ σ': state} {ty: LogicType}:
  IncLoLang.lang_semantics (C** ;; C) ty σ σ' → IncLoLang.lang_semantics (C**) ty σ σ' :=
begin
  intro h,
  cases h,
  {
    have H: ∃ N, lang_semantics (repeat C N) ty σ σ',
    {
      cases h_H1,
      use h_H1_i.succ,
      rw repeat,
      exact lang_semantics.seq_ty h_H1_h h_H2,
    },
    cases H with N,
    exact lang_semantics.star N H_h,
  },
  { exact h_H1, },
end

lemma assign_order {σ x y v₁ v₂} (Hxy: x ≠ y) :
  σ{x ↦ v₁}{y ↦ v₂} = σ{y ↦ v₂}{x ↦ v₁} :=
begin
  apply funext,
  intro z,
  by_cases h₁ : z = x,
  { finish, },
  by_cases h₂ : z = y,
  repeat{ finish, },
end

lemma assign_order_eq {σ x v₁ v₂}:
  σ{x ↦ v₁}{x ↦ v₂} = σ{x ↦ v₂} :=
begin
  apply funext,
  intro z,
  by_cases h₁ : z = x,
  repeat { finish, },
end

/-! ## Free lemmas -/

lemma mod_sub_free (C: stmt):
  Mod C ⊆ C.Free :=
begin
  induction C with v r _ C₁ C₂ hC₁ hC₂ C₁ C₂ hC₁ hC₂ _ h,
  case stmt.skip {
    rw Mod,
    exact stmt.skip.Free.empty_subset,
  },
  case stmt.assign {
    rw Mod,
    rw stmt.Free,
    exact ({v}: set string).subset_union_left (expression.Free r),
  },
  case stmt.non_det_assign {
    rw Mod,
    rw stmt.Free,
  },
  case stmt.seq {
    rw Mod,
    rw stmt.Free,
    exact set.union_subset_union hC₁ hC₂,
  },
  case stmt.choice {
    rw Mod,
    rw stmt.Free,
    exact set.union_subset_union hC₁ hC₂,
  },
  case stmt.star {
    rw Mod,
    rw stmt.Free,
    exact h,
  },
  case stmt.local_var {
    rw Mod,
    rw stmt.Free,
    exact set.diff_subset_diff_left C_ih,
  },
  case stmt.error {
    rw Mod,
    rw stmt.Free,
  },
  case stmt.assumes {
    rw Mod,
    exact (stmt.assumes C).Free.empty_subset,
  },
end

lemma not_free_expression {e: expression} {x}: 
  (¬e.Free x) → ∀ σ v, e σ = e (σ{x ↦ v}) :=
begin
  intro h,
  unfold expression.Free at h,
  push_neg at h,
  exact h,
end

lemma not_free_prop {e: prop} {x}: 
  (¬e.Free x) → ∀ σ v, e σ ↔ e (σ{x ↦ v}) :=
begin
  intro h,
  unfold prop.Free at h,
  push_neg at h,
  intros σ v,
  split,
  { exact h σ v, },
  {
    specialize h (σ{x ↦ v}) (σ x),
    have H: σ{x ↦ v}{x ↦ σ x} = σ, {
      funext,
      by_cases x = name',
      { finish, },
      { finish, }
    },
    rw H at h,
    exact h,
  }
end

lemma free_language_semantics (C: stmt) (x: string):
  (¬C.Free x) → (∀ σ σ' ty v, lang_semantics C ty σ σ' → lang_semantics C ty (σ{x ↦ v}) (σ'{x ↦ v})) :=
begin
  induction C with 
    y 
    e y 
    C₁ C₂ C₁h C₂h 
    C₁ C₂ C₁h C₂h
    C Ch
    z C,
  case stmt.skip {
    intros h₁ σ σ' ty v h,
    cases h,
    exact lang_semantics.skip,
  },
  case stmt.assign {
    intros h₁ σ σ' ty v h₂,
    cases h₂,
    by_cases x = y,
    {
      exfalso,
      rw stmt.Free at h₁,
      apply h₁,
      left,
      exact set.mem_singleton_iff.mpr h,
    },
    {
      rw ← state.update,
      rw assign_order (ne.symm h),
      -- have H: (λ (name' : string), σ name') = σ, {exact rfl}
      rw stmt.Free at h₁,
      have H: e σ = e (σ{x ↦ v}), {
        by_contra,
        have H2: x ∈ e.Free, {
          use σ,
          use v,
        },
        apply h₁,
        right,
        exact H2,
      },
      rw H,
      exact lang_semantics.assign,
    }
  },
  case stmt.non_det_assign {
    intros h₁ σ σ' ty v h₂,
    cases h₂,
    by_cases x = y,
    {
      exfalso,
      rw stmt.Free at h₁,
      apply h₁,
      exact set.mem_singleton_iff.mpr h,
    },
    {
      rw ← state.update,
      rw assign_order (ne.symm h),
      -- have H: (λ (name' : string), σ name') = σ, {exact rfl}
      rw stmt.Free at h₁,

      exact lang_semantics.non_det_assign h₂_v,
    }
  },
  case stmt.seq {
    intros h₁ σ σ' ty v h₂,
    rw stmt.Free at h₁,
    specialize C₁h (by {
      by_contra,
      apply h₁,
      left,
      exact h,
    }),
    specialize C₂h (by {
      by_contra,
      apply h₁,
      right,
      exact h,
    }),
    cases h₂,
    {
      specialize C₁h σ h₂_t LogicType.ok v h₂_H1,
      specialize C₂h h₂_t σ' ty v h₂_H2,
      exact lang_semantics.seq_ty C₁h C₂h,
    },
    {
      specialize C₁h σ σ' LogicType.er v h₂_H1,
      exact lang_semantics.seq_er_1 C₁h,
    },
  },
  case stmt.choice {
    intros h₁ σ σ' ty v h₂,
    rw stmt.Free at h₁,

    cases h₂,
    {
      specialize C₁h (by {
        by_contra,
        apply h₁,
        left,
        exact h,
      }) σ σ' ty v h₂_h,
      exact lang_semantics.choice_left C₁h,
    },
    {
      specialize C₂h (by {
        by_contra,
        apply h₁,
        right,
        exact h,
      }) σ σ' ty v h₂_h,
      exact lang_semantics.choice_right C₂h,
    },
  },
  case stmt.star {
    intros h₁ σ σ' ty v h₂,
    rw stmt.Free at h₁,
    specialize Ch h₁,
    cases h₂,
    use h₂_i,
    revert σ σ' ty,
    induction h₂_i,
    {
      intros σ σ' ty h,
      rw repeat at h,
      cases h,
      rw repeat,
      exact lang_semantics.skip,
    },
    {
      intros σ σ' ty h,
      rw repeat,
      rw repeat at h,
      cases h,
      {
        exact lang_semantics.seq_ty 
          (h₂_i_ih σ h_t LogicType.ok h_H1)
          (Ch h_t σ' ty v h_H2),
      },
      { exact lang_semantics.seq_er_1 ( h₂_i_ih σ σ' LogicType.er h_H1 ), }
    }
  },
  case stmt.local_var {
    intros h₁ σ σ' ty v,
    rw stmt.Free at h₁,
    by_cases H: x = z,
    {
      cases H,
      intro h,
      cases h,
      rw ← state.update,
      rw ← state.update,
      rw assign_order_eq,
      rw assign_order_eq,
      exact lang_semantics.local_var h_h,
    },
    {
      have h₂: x ∉ C.Free, {
        by_contra,
        apply h₁,
        split,
        { exact h, },
        { 
          by_contra, 
          apply H, 
          exact set.mem_singleton_iff.1 h,
        },
      },
      specialize C_ih h₂,
      intro h,
      cases h,
      rw ← state.update,
      rw ← state.update,
      rw assign_order (ne.symm H),
      rw assign_order (ne.symm H),
      exact lang_semantics.local_var (C_ih h_s₁ h_s₂ ty v h_h)
    },
  },
  case stmt.error {
    intros h₁ σ σ' ty v h,
    cases h,
    exact lang_semantics.error,
  },
  case stmt.assumes {
    intros h₁ σ σ' ty v h,
    cases h,
    rw stmt.Free at h₁,
    rw prop.Free at h₁,
    push_neg at h₁,
    exact lang_semantics.assumes_ok (h₁ σ v h_h),
  },
end

lemma assign_semantics {x σ σ' ty} {e: expression}: 
  lang_semantics ([x ↣ e]) ty σ σ' → σ{x ↦ e σ} = σ' ∧ ty = LogicType.ok:=
begin
  intro h,
  cases h,
  split,
  repeat { refl },
end

lemma non_det_assign_semantics {x σ σ' ty}: 
  lang_semantics (stmt.non_det_assign x) ty σ σ' → ∃ v, σ' = σ{x ↦ v} ∧ ty = LogicType.ok :=
begin
  intro h,
  cases h,
  use h_v,
  split,
  repeat { refl },
end

lemma p_thing_free {x v} {P: state -> Prop} :
  prop.Free (P{ x ↣ v }) ⊆ prop.Free P \ {x} :=
begin
  intros y hy,
  unfold prop.Free at hy,
  unfold prop.Free,
  unfold p_thing at hy,
  cases hy with σ,
  use σ{x ↦ v},
  have Hxy: x ≠ y,
  {
    by_contra,
    cases h,
    cases hy_h with v,
    rw assign_order_eq at hy_h_h,
    finish,
  },
  {
    cases hy_h with n hn,
    use n,
    rw assign_order Hxy,
    exact hn,
  },
  {
    intro h,
    finish,
  },
end



-- lemma free_assign {x e}: (stmt.Free ([x ↣ e])) ⊆ (expression.Free e) ∪ {x} :=
-- begin
--   intros y hy,
--   by_cases x = y,
--   {
--     cases h,
--     right,
--     exact set.mem_singleton x,
--   },
--   {
--     left,
--     intros σ v,
--     specialize hy σ (σ{x ↦ e σ}) LogicType.ok v,
--     have H := hy (lang_semantics.assign),

--     have H2 := assign_semantics H,
--     have H3 : (σ{y ↦ v}{x ↦ e (σ{y ↦ v})}) x = e (σ{y ↦ v}), {
--       exact state.update_apply x (e (σ{y ↦ v})) (σ{y ↦ v}),
--     },

--     rw ← H3,
  
--     have H4 : σ{x ↦ e σ}{y ↦ v} x = e σ, { finish },
--     rw ← H4,

--     exact congr (eq.symm H2.left) rfl,
--   },
-- end

-- lemma free_assign_2 {x e}: (expression.Free e) \ {x} ⊆ (stmt.Free ([x ↣ e])) :=
-- begin
--   intros y hy,
--   intros σ σ' ty v,
--   cases hy,

--   specialize hy_left σ v,
--   intro h,
--   cases h,
--   rw ← state.update,
--   rw assign_order (ne.symm hy_right),
--   rw hy_left,
--   exact lang_semantics.assign,
-- end

-- lemma free_non_det_assign {x}: ∀ n, n ∈ (stmt.Free (stmt.non_det_assign x)) :=
-- begin
--   unfold stmt.Free,

--   intro n,
--   by_cases n = x,
--   {
--     cases h,
--     intros σ σ' ty v hls,
--     cases hls,
--     have H: (λ (name' : string), ite (name' = x) hls_v (σ name')){x ↦ v} = σ{x ↦ v}{x ↦ v},
--     {
--       funext,
--       by_cases name' = x,
--       { finish, },
--       { finish, }
--     },
--     rw H,
--     exact lang_semantics.non_det_assign v,
--   },
--   {
--     intros σ σ' ty v hls,
--     cases hls,
--     rw ← state.update,
--     rw assign_order (ne.symm h),
--     exact lang_semantics.non_det_assign hls_v,
--   },
-- end

-- lemma substitution_rule {ty C y x} {σ σ' : state} (Hyx: y ≠ x) (Hfreey: y ∈ stmt.Free C):
--   lang_semantics C ty (σ) (σ') -> 
--     -- If C can take σ to σ'
--     lang_semantics (C{y // x}) ty (σ⟨ y // x⟩) (σ'⟨ y // x ⟩) :=
--     -- Then C(y/x) can take σ with y set to x's value in σ to σ' with y set to x's value in σ' 
-- begin
--   revert ty σ σ',

--   induction C with z e z,
--   case stmt.skip {
--     -- Skip case is trivial as σ = σ'
--     intros _ σ _ h,
--     cases h,
--     exact lang_semantics.skip,
--   },
--   case stmt.assign {
--     intro s,
--     have H := free_assign Hfreey,
--     intros σ σ' hls,
--     cases hls,
--     cases hls,
--     rw stmt.substitute,
--     cases H,
--     { -- case y ∈ Free e
--       sorry,
--     },
--     { -- case y = z
--       sorry,
--     },
--   },
--   case stmt.non_det_assign {
--     intros ty σ σ' hls,

--     by_cases x = z,
--     {
--       cases h,
--       rw stmt.substitute,
--       cases hls,
--       unfold state.substitute,
--       have H: σ{x ↦ σ y}{x ↦ (σ y)} = (λ (name' : string), ite (name' = x) hls_v (σ name')){x ↦ ite (y = x) hls_v (σ y)}, 
--       {
--         funext,
--         by_cases name' = x,
--         { finish, },
--         { finish, },
--       },
--       rw ← H,
--       exact lang_semantics.non_det_assign (σ y),
--     },

--     have H: ∃ v, σ'⟨y//x⟩ = σ⟨y//x⟩{z ↦ v},
--     {
--       cases hls,
--       use hls_v,
--       rw state.substitute,
--       simp,
--       rw ← state.update,
--       rw ← state.update at hls,

--       by_cases H₂: x = y,
--       {
--         cases H₂,
--         funext,
--         rw if_neg h,
--         rw assign_order h,
--       },
--       {
--         funext,
--         rw if_neg h,

--       }
--       -- ow


--     },

--     have H2: ty = LogicType.ok, { cases hls, refl, },
--     rw H2,

--     -- | non_det_assign {x s v} :
--     --   lang_semantics (IncLoLang.stmt.non_det_assign x) LogicType.ok s (s{x ↦ v})

--     rw stmt.substitute,
--     cases H,
--     rw H_h,

--     exact lang_semantics.non_det_assign H_w,
--   },

--   sorry,
--   sorry,
--   sorry,
--   sorry,
--   sorry,
--   sorry,
-- end

end IncLoLang

/-
      intros σ σ' h,
      cases h,
      rw stmt.substitute,
      by_cases Hx: x = z,
      {
        rw if_pos Hx,
        rw state.substitute,
        simp,
        have H2 := H σ (σ x),

        have h2: σ{z ↦ e σ}⟨y//x⟩ = σ⟨y//x⟩{y ↦ (λ (σ : state), e (σ{y ↦ σ x})) (σ⟨y//x⟩)},
        {
          simp,
          rw ← Hx,
          unfold state.substitute,
          rw assign_order_eq,

          funext,
          rw ← H (σ{x ↦ σ y}) (σ{x ↦ σ y} x),
          by_cases hx: name' = x,
          { finish, },
          { 
            by_cases hy: name' = y,
            {
              rw hy,
              rw hy at hx,
              unfold state.update,
              rw if_neg hx,
              have H3: y = y, {refl,},
              rw if_pos H3,
              rw ← state.update,

              cases h,
              
            },
            {

            }
          }
        },
        rw ← state.update,

        rw h2,
        exact lang_semantics.assign,
-/