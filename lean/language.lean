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

@[simp] lemma state.update_apply_ne (name name' : string) (val : ℕ) (s : state)
    (h : name' ≠ name) :
  s{name ↦ val} name' = s name' :=
begin
  unfold state.update,
  exact if_neg h,
end

@[simp] lemma state.update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma state.update_swap (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state)
    (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma state.update_id (name : string) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

@[simp] lemma state.update_same_const (name : string) (val : ℕ) :
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
-- | local_var       : string → stmt → stmt
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
-- | local_var {C s₁ s₂ ty} (x: string) (v: ℕ) (h: lang_semantics C ty s₁ s₂):
--   lang_semantics ([loc x . C]) ty (s₁{x ↦ v}) (s₂{x ↦ v})

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
-- | [loc z . C]               := (stmt.Free C)
-- | [loc z . C]               := (stmt.Free C) \ {z}
| stmt.error                := {}
| (stmt.assumes P)          := prop.Free P

/-! # Substitute-/

def state.substitute : string → string → state → state
-- | y x := λ σ, σ{y ↦ σ x}
| y x := λ σ, σ{y ↦ σ x}{x ↦ 0}

notation σ `⟨` vto `//` vfrom `⟩` :=  state.substitute vto vfrom σ

def prop.substitute : string → string → prop → prop
| x s P := λ σ, P (σ{x ↦ σ s})

notation P `[` val `//` name `]` :=  prop.substitute name val P

def expression.substitute : string → string → expression → expression
| x y e := λ σ, e (σ⟨ x // y ⟩)

def stmt.substitute : string → string → stmt → stmt
| x y stmt.skip                 := stmt.skip
| x y ([z ↣ e₂])                := if x = z then [y ↣ λ σ, ((expression.substitute x y e₂) σ)] else [z ↣ λ σ, ((expression.substitute x y e₂) σ)]  -- PUT X BACK!
| x y (stmt.non_det_assign z)   := if x = z then stmt.non_det_assign y else stmt.non_det_assign z
| x y (C₁ ;; C₂)                := (stmt.substitute x y C₁) ;; (stmt.substitute x y C₂)
| x y (C₁ <+> C₂)               := (stmt.substitute x y C₁) <+> (stmt.substitute x y C₂)
| x y (C**)                     := (stmt.substitute x y C)**
-- | x y [loc z . C]               := if x = z then [loc x . C] else [loc z . (stmt.substitute x y C)]
-- | x y [loc z . C]               := if x = z then [loc x . C] else (if y = z then C else [loc z . (stmt.substitute x y C)])
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
-- | (IncLoLang.stmt.local_var x C) := Mod C \ {x}

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
  -- case stmt.local_var {
  --   rw Mod,
  --   rw stmt.Free,
  --   exact set.diff_subset_diff_left C_ih,
  -- },
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
      rw state.update_swap _ _ _ _ _ (h),
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
      rw state.update_swap _ _ _ _ _ h,
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
  -- case stmt.local_var {
  --   intros h₁ σ σ' ty v,
  --   rw stmt.Free at h₁,
  --   by_cases H: x = z,
  --   {
  --     cases H,
  --     intro h,
  --     cases h,
  --     rw ← state.update,
  --     rw ← state.update,
  --     rw assign_order_eq,
  --     rw assign_order_eq,
  --     exact lang_semantics.local_var x v h_h,
  --   },
  --   {
  --     have h₂: x ∉ C.Free, {
  --       by_contra,
  --       apply h₁,
  --       split,
  --       { exact h, },
  --       { 
  --         by_contra, 
  --         apply H, 
  --         exact set.mem_singleton_iff.1 h,
  --       },
  --     },
  --     specialize C_ih h₂,
  --     intro h,
  --     cases h,
  --     rw ← state.update,
  --     rw ← state.update,
  --     rw assign_order (ne.symm H),
  --     rw assign_order (ne.symm H),
  --     exact lang_semantics.local_var _ _ (C_ih h_s₁ h_s₂ ty v h_h)
  --   },
  -- },
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
    rw state.update_override at hy_h_h,
    finish,
  },
  {
    cases hy_h with n hn,
    use n,
    -- rw assign_order Hxy,
    rw state.update_swap _ _ _ _ _ (ne.symm Hxy),
    exact hn,
  },
  {
    intro h,
    finish,
  },
end

lemma free_assign {x e}:  (expression.Free e) ∪ {x} ⊆ (stmt.Free ([x ↣ e])):=
begin
  intros y hy,
  by_cases x = y,
  {
    cases h,
    unfold stmt.Free,
    left,
    exact set.mem_singleton x,
  },
  {
    -- rcases hy with ⟨ x, y ⟩, 
    cases hy,
    {
      -- rcases hy with ⟨σ, ⟨v, hσ⟩⟩,
      rw stmt.Free,
      right, 
      exact hy,
    },
    {
      exfalso, cases hy, apply h, refl,
    }
  },
end

lemma assign_case {ty y x z e} {σ σ' : state} (Hyx: y ≠ x) (Hfreey: y ∉ ([z ↣ e].Free)):
  lang_semantics ([z ↣ e]) ty (σ) (σ') →  
    lang_semantics ([z ↣ e]{y // x}) ty (σ⟨ y // x⟩) (σ'⟨ y // x ⟩) :=
begin
  have H := (set.compl_subset_compl.mpr free_assign) Hfreey,
  have H₁ : y ∉ e.Free, { by_contra, finish, },
  have H₁ := not_free_expression H₁,
  simp at H₁,

  have H₂ : y ≠ z, {
    by_contra,
    finish,
  },

  intro hls,
  cases hls,
  cases hls,
  rw stmt.substitute,

  by_cases hx: x = z,
  {
    rw if_pos hx,
    cases hx,
    rw ← state.update,
    rw expression.substitute,
    simp,

    have H: σ{x ↦ e σ}⟨y//x⟩= σ⟨y//x⟩{y ↦ (λ (σ : state), e (σ⟨x//y⟩)) (σ⟨y//x⟩)}, 
    {
      ext z,
      simp,

      unfold state.update,
      unfold state.substitute,
      by_cases hx: x = z,
      {finish,},
      {
        by_cases hy: y = z,
        {
          cases hy,
          simp,
          finish,
        },
        {
          simp,
          unfold state.update,
          finish,
        },
      }
    },
    
    rw H,
    exact lang_semantics.assign,
  },
  {
    rw if_neg hx,
    rw ← state.update,
    rw state.substitute,
    simp,
    rw state.update_swap _ _ _ _ _ H₂,
    rw state.update_swap _ _ _ _ _ hx,
    have H: σ{z ↦ e σ} x = σ x, {
      funext, finish,
    },
    rw H,
    rw expression.substitute,
    have H: e σ = (λ (σ : state), e (σ⟨x//y⟩)) (σ{y ↦ σ x}{x ↦ 0}), {
      simp,
      rw state.substitute,
      simp,
      rw ← state.update_swap _ _ _ _ _ Hyx,
      rw state.update_override,
      have H: σ{x ↦ σ{y ↦ σ x}{x ↦ 0} y} = σ, {
        funext, finish,
      },
      rw H,
      exact H₁ σ 0,
    },
    rw H,
    exact lang_semantics.assign,
  },
end

lemma substitution_rule {ty C y x} {σ σ' : state} (Hyx: y ≠ x) (Hfreey: y ∉ stmt.Free C):
  lang_semantics C ty (σ) (σ') → 
    -- If C can take σ to σ'
    lang_semantics (C{y // x}) ty (σ⟨ y // x⟩) (σ'⟨ y // x ⟩) :=
    -- Then C(y/x) can take σ with y set to x's value in σ to σ' with y set to x's value in σ' 
begin
  revert ty σ σ',

  induction C with z e z 
    C₁ C₂ hC₁ hC₂
    C₁ C₂ hC₁ hC₂
    C hC,
    -- z C hC,
  case stmt.skip {
    -- Skip case is trivial as σ = σ'
    intros _ σ _ h,
    cases h,
    exact lang_semantics.skip,
  },
  case stmt.assign {
    intros ty σ σ' hls,
    exact assign_case Hyx Hfreey hls,
  },
  case stmt.non_det_assign {
    intros ty σ σ' hls,

    by_cases x = z,
    {
      cases h,
      rw stmt.substitute,
      cases hls,
      unfold state.substitute,
      rw if_pos (rfl),
      rw ← state.update,
      rw state.update_swap _ _ _ _ _ Hyx,
      rw if_pos (rfl),
      simp,
      rw ← state.update_swap _ _ _ _ _ Hyx,
      rw ← state.update_swap _ _ _ _ _ Hyx,
      have H: σ{x ↦ 0}{y ↦ hls_v} = σ{x ↦ 0}{y ↦ σ x}{y ↦ hls_v}, { rw state.update_override, },
      rw H,
      exact lang_semantics.non_det_assign hls_v,
    },
    {
      rw stmt.substitute,
      cases hls,
      unfold state.substitute,
      rw if_neg h,
      rw ← state.update,
      rw if_neg h,
      by_cases H₂: z = y,
      {
        cases H₂,
        rw state.update_override,
        rw state.update_swap _ _ _ _ _ h,
        have H: σ{x ↦ 0}{y ↦ σ x} = σ{x ↦ 0}{y ↦ σ x}{y ↦ σ x}, { rw state.update_override, },
        nth_rewrite 1 H,
        exact lang_semantics.non_det_assign (σ x),
      },
      {
        rw state.update_swap _ _ _ _ _ (ne.symm H₂),
        rw state.update_swap _ _ _ _ _ h,
        exact lang_semantics.non_det_assign hls_v,
      }
    },
  },
  case stmt.seq {
    intros ty σ σ' hls,
    cases hls,
    {
      specialize hC₁ (by {
        by_contra,
        apply Hfreey,
        left,
        exact h,
      }) hls_H1,
      specialize hC₂ (by {
        by_contra,
        apply Hfreey,
        right,
        exact h,
      }) hls_H2,
      rw stmt.substitute,
      exact lang_semantics.seq_ty hC₁ hC₂,
    },
    {
      specialize hC₁ (by {
        by_contra,
        apply Hfreey,
        left,
        exact h,
      }) hls_H1,
      rw stmt.substitute,
      exact lang_semantics.seq_er_1 hC₁,
    }
  },
  case stmt.choice {
    intros ty σ σ' hls,
    cases hls,
    {
      specialize hC₁ (by {
        by_contra,
        apply Hfreey,
        left,
        exact h,
      }) hls_h,
      rw stmt.substitute,
      exact lang_semantics.choice_left hC₁,
    },
    {
      specialize hC₂ (by {
        by_contra,
        apply Hfreey,
        right,
        exact h,
      }) hls_h,
      rw stmt.substitute,
      exact lang_semantics.choice_right hC₂,
    }
  },
  case stmt.star {
    intros ty σ σ' hls,
    cases hls,
    rw stmt.substitute,
    use hls_i,
    revert ty σ σ' ,
    induction hls_i,
    {
      intros ty σ σ' hls_h,
      rw repeat at hls_h,
      cases hls_h,
      rw repeat,
      exact lang_semantics.skip,
    },
    {
      intros ty σ σ' hls_h,
      rw repeat at hls_h,
      cases hls_h,
      {
        specialize hls_i_ih hls_h_H1,
        rw stmt.Free at Hfreey,
        specialize hC Hfreey hls_h_H2, 
        rw repeat,
        exact lang_semantics.seq_ty hls_i_ih hC,
      },
      {
        specialize hls_i_ih hls_h_H1,
        rw repeat,
        exact lang_semantics.seq_er_1 hls_i_ih,
      },
    },
  },
  -- case stmt.local_var {
  --   intros ty σ σ' hls,
  --   cases hls,
  --   rw stmt.substitute,
  --   by_cases x = z,
  --   {
  --     cases h,
  --     rw if_pos h,
  --     rw stmt.Free at Hfreey,
  --     have H : y ∉ C.Free, { finish, },
  --     rw ← state.update,
  --     rw ← state.update,
  --     rw state.substitute,
  --     simp,
  --     have H₂ := free_language_semantics C y H,
  --     rw ← assign_order Hyx,
  --     rw ← assign_order Hyx,
  --     rw assign_order_eq,
  --     rw assign_order_eq,
  --     specialize H₂ hls_s₁ hls_s₂ ty hls_v hls_h, 
  --     exact lang_semantics.local_var _ _ H₂,
  --   },
  --   {
  --     rw if_neg h,
  --     rw stmt.Free at Hfreey,
  --     by_cases y = z,
  --     {
  --       cases h,
  --       rw ← state.update,
  --       rw state.substitute,
  --       rw ← state.update,
  --       simp,
  --       have H1: hls_s₁{y ↦ hls_v} x = hls_s₁ x, { unfold state.update, finish, },
  --       have H2: hls_s₂{y ↦ hls_v} x = hls_s₂ x, { unfold state.update, finish, },
  --       rw H1, rw H2,
  --       sorry,
  --        -- [loc z. z = 5]
  --        -- [loc z. x = 5](z//x)
  --        -- [loc z. z = 5](z//x) !! Need to move to fresh
  --       -- exact lang_semantic.local_var y hls_v (hC Hfreey hls_h),
  --       -- rw stmt.substitute,
  --       -- x ≠ b (σ1, σ2) ∈ ⟦local x . C⟧ and y ∉ Free C ⇒ (σ1(y/b), σ2(y/b)) ∈ ⟦local x . C(y/b)⟧
  --       -- ({b = 1}, {b = 2}) ∈ ⟦local y . b = 2⟧ ⇒ ({y = 1}, {y = 2}) ∈ ⟦local y . y = 2⟧
  --     },
  --     {
  --       have H: y ∉ C.Free, { by_contra, finish, },
  --       specialize hC H hls_h,
  --       rw ← state.update,
  --       rw ← state.update,
  --       simp,
  --       have H1: ∀ σ, ((σ{z ↦ hls_v})⟨y//x⟩) = ((σ⟨y//x⟩){z ↦ hls_v}), {
  --         intro σ,
  --         rw state.substitute,
  --         funext,
  --         simp,
  --         unfold state.update,
  --         by_cases name' = x, { cases h, finish, },
  --         by_cases name' = y, { cases h, finish, },
  --         by_cases name' = z, { cases h, finish, },
  --         finish,
  --       },
  --       rw (H1 hls_s₁),
  --       rw (H1 hls_s₂),
  --       exact lang_semantics.local_var _ _ hC,
  --     },
  --   },
  -- },
  {
    intros ty σ σ' hls,
    cases hls,
    rw stmt.substitute,
    exact lang_semantics.error,  
  },
  {
    intros ty σ σ' hls,
    cases hls,
    rw stmt.substitute,
    have H: (C[y//x]) (σ⟨y//x⟩), { 
      unfold prop.substitute,
      unfold state.substitute,
      rw state.update_override,
      have H: σ{y ↦ σ x}{x ↦ σ{y ↦ σ x}{x ↦ 0} y} = σ{y ↦ σ x}, {
        unfold state.update,
        funext,
        finish,
      },
      rw H,
      rw stmt.Free at Hfreey,
      apply (not_free_prop Hfreey σ (σ x)).1,
      exact hls_h,
    },
    exact lang_semantics.assumes_ok H,
  },
end

lemma stmt_free_unchanged {x: string} {C: stmt} {σ σ': state} {ty: LogicType}: 
  (lang_semantics C ty σ σ') ∧ (x ∉ C.Free) → σ x = σ' x :=
begin 
  revert σ σ' ty,
  induction C with 
    y e
    y
    C₁ C₂ hC₁ hC₂
    C₁ C₂ hC₁ hC₂
    C Ch,
  case stmt.skip {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    cases hls,
    refl,
  },
  case stmt.assign {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    cases hls,
    unfold stmt.Free at hxFree,
    have H: x ≠ y, { finish, },
    simp,
    rw if_neg H,
  },
  case stmt.non_det_assign {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    cases hls,
    unfold stmt.Free at hxFree,
    have H: x ≠ y, { finish, },
    simp,
    rw if_neg H,
  },
  case stmt.seq {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    have H₁: x ∉ C₁.Free, {by_contra, apply hxFree, left, exact h,},
    have H₂: x ∉ C₂.Free, {by_contra, apply hxFree, right, exact h,},
    cases hls,
    {
      specialize hC₁ (⟨hls_H1, H₁⟩),
      specialize hC₂ (⟨hls_H2, H₂⟩),
      rw hC₁,
      exact hC₂,
    },
    { exact hC₁ (⟨hls_H1, H₁⟩), },
  },
  case stmt.choice {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    have H₁: x ∉ C₁.Free, {by_contra, apply hxFree, left, exact h,},
    have H₂: x ∉ C₂.Free, {by_contra, apply hxFree, right, exact h,},
    cases hls,
    {
      specialize hC₁ (⟨hls_h, H₁⟩),
      exact hC₁,
    },
    {
      specialize hC₂ (⟨hls_h, H₂⟩),
      exact hC₂,
    },
  },
  case stmt.star {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    cases hls,
    revert ty σ σ', 
    induction hls_i with n hC' hC',
    {
      intros _ _ _ hls_h,
      rw repeat at hls_h,
      cases hls_h,
      refl,
    },
    {
      intros ty σ σ' hls,
      rw repeat at hls,
      rw stmt.Free at hxFree,
      cases hls,
      {
        specialize Ch (⟨hls_H2, hxFree⟩),
        specialize hC' hls_H1,
        rw hC',
        exact Ch,
      },
      {
        specialize hC' hls_H1,
        exact hC',
      },
    }
  },
  case stmt.error {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    cases hls,
    refl,
  },
  case stmt.assumes {
    rintros σ σ' ty ⟨ hls, hxFree ⟩,
    cases hls,
    refl,
  },
end

lemma for_all_free_expression {e: expression} {σ σ': state } (H: ∀ x ∈ e.Free, σ x = σ' x): e σ = e σ' :=
begin 
  -- Help??
  sorry,
  -- trivial,
end

end IncLoLang
