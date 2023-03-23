import lean.incorrectness_logic

namespace IncorrectnessCompleteness

inductive IncorrectnessProof : IncLoLang.prop → IncLoLang.stmt → IncLoLang.prop → IncLoLang.LogicType → Prop
| empty_under_approx {P: IncLoLang.prop} {ty: IncLoLang.LogicType} {C: IncLoLang.stmt}: 
  IncorrectnessProof P C (λ _, false) ty
| consequence (P Q P' Q': IncLoLang.prop) {ty: IncLoLang.LogicType} {C: IncLoLang.stmt} (Hp: ∀ σ, P σ → P' σ) (Hq: ∀ σ, Q' σ → Q σ) (H: IncorrectnessProof P C Q ty): 
  IncorrectnessProof P' C Q' ty
| disjunction {P₁ Q₁ P₂ Q₂: IncLoLang.prop} {ty: IncLoLang.LogicType} {C: IncLoLang.stmt} (H₁: IncorrectnessProof P₁ C Q₁ ty) (H₁: IncorrectnessProof P₂ C Q₂ ty): 
  IncorrectnessProof (λ σ, P₁ σ ∨ P₂ σ) C (λ σ, Q₁ σ ∨ Q₂ σ) ty
| unit_ok {P: IncLoLang.prop}: 
  IncorrectnessProof P IncLoLang.stmt.skip P IncLoLang.LogicType.ok
| unit_er {P: IncLoLang.prop}: 
  IncorrectnessProof P IncLoLang.stmt.skip (λ _, false) IncLoLang.LogicType.er
| sequencing_short {P Q: IncLoLang.prop} {C₁ C₂: IncLoLang.stmt} (H: IncorrectnessProof P C₁ Q IncLoLang.LogicType.er): 
  IncorrectnessProof P (C₁;;C₂) Q IncLoLang.LogicType.er
| sequencing_normal {P Q R: IncLoLang.prop} {C₁ C₂: IncLoLang.stmt} {ty: IncLoLang.LogicType}
  (H₁: IncorrectnessProof P C₁ Q IncLoLang.LogicType.ok)
  (H₂: IncorrectnessProof Q C₂ R ty) : 
  IncorrectnessProof P (C₁;;C₂) R ty
| iterate_zero {P: IncLoLang.prop} {C: IncLoLang.stmt} :
  IncorrectnessProof P (C**) P IncLoLang.LogicType.ok
| iterate_non_zero {P Q: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}
  (H: IncorrectnessProof P (C** ;; C) Q ty) :
  IncorrectnessProof P (C**) Q ty
| backwards_variant {N: ℕ} {P: ℕ → IncLoLang.prop} {C: IncLoLang.stmt} 
  (H: ∀ n, IncorrectnessProof (P n) C (P (n+1)) IncLoLang.LogicType.ok) :
  IncorrectnessProof (P 0) (C**) (P N) IncLoLang.LogicType.ok
| choice_left {P Q: IncLoLang.prop} {C₁ C₂: IncLoLang.stmt} {ty: IncLoLang.LogicType} 
  (H: IncorrectnessProof P C₁ Q ty) :
  IncorrectnessProof P (C₁ <+> C₂) Q ty
| choice_right {P Q: IncLoLang.prop} {C₁ C₂: IncLoLang.stmt} {ty: IncLoLang.LogicType} 
  (H: IncorrectnessProof P C₂ Q ty) :
  IncorrectnessProof P (C₁ <+> C₂) Q ty
| error_ok {P: IncLoLang.prop}:
  IncorrectnessProof P (IncLoLang.stmt.error) (λ_, false) IncLoLang.LogicType.ok
| error_er {P: IncLoLang.prop}:
  IncorrectnessProof P (IncLoLang.stmt.error) P IncLoLang.LogicType.er
| assume_ok {P B: IncLoLang.prop}:
  IncorrectnessProof P (IncLoLang.stmt.assumes B) (λ σ, P σ ∧ B σ) IncLoLang.LogicType.ok
| assume_er {P B: IncLoLang.prop}:
  IncorrectnessProof P (IncLoLang.stmt.assumes B) (λ σ, false) IncLoLang.LogicType.er
| assignment_ok {P: IncLoLang.prop} {e: IncLoLang.expression} {x: string} :
  IncorrectnessProof P ([x ↣ e]) (λ σ', (∃ x', (P{x ↣ x'} σ') ∧ σ' x = e (σ'{x ↦ x'}))) IncLoLang.LogicType.ok
| assignment_er {P: IncLoLang.prop} {e: IncLoLang.expression} {x: string} :
  IncorrectnessProof P ([x ↣ e]) (λ σ', false) IncLoLang.LogicType.er
| non_det_assignment_ok {P: IncLoLang.prop} {x: string} :
  IncorrectnessProof P (IncLoLang.stmt.non_det_assign x) (λ σ', (∃ v, (P{x ↣ v} σ'))) IncLoLang.LogicType.ok
| non_det_assignment_er {P: IncLoLang.prop} {x: string} :
  IncorrectnessProof P (IncLoLang.stmt.non_det_assign x) (λ σ', false) IncLoLang.LogicType.er
| constancy {P Q F: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}
  (HC: IncorrectnessProof P C Q ty) 
  (Hf: C.Mod ∩ F.Free = ∅) :
  IncorrectnessProof (λ σ, P σ ∧ F σ) C (λ σ', Q σ' ∧ F σ') ty
| substitution_1 {P Q: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType} {e: IncLoLang.expression} {x: string}
  (HC: IncorrectnessProof P C Q ty) 
  (HB: (∃ B: set string, (e.FreeProp B ∧ B.finite)))
  (He: (e.Free ∪ {x}) ∩ C.Free = ∅): 
  IncorrectnessProof (λ σ, P (σ{x ↦ e σ})) C (λ σ, Q (σ{x ↦ e σ})) ty
| substitution_2 {P Q: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType} {x y: string}
  (H₁: [* P *]C[* Q *]ty) 
  (H₂: y ∉ C.Free ∪ P.Free ∪ Q.Free) 
  (H₃: x ≠ y): 
  IncorrectnessProof (P[y//x]) (C{y // x}) (Q[y//x]) ty


lemma IncorectnessProof.soundness {P Q: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}:
  IncorrectnessProof P C Q ty → [* P *]C[* Q *]ty :=
begin
  intro h,
  induction h,

  case empty_under_approx { exact IncLogic.empty_under_incorrect, },
  case consequence { exact IncLogic.consequence_incorrect h_ih h_Hq h_Hp, },
  case disjunction { refine IncLogic.disjunction_incorrect h_ih_H₁ h_ih_H₁_1},
  case unit_ok { refine IncLogic.unit_incorrect_ok},
  case unit_er { refine IncLogic.unit_incorrect_err},
  case sequencing_short { refine IncLogic.seq_short_circuit_incorrect h_ih, },
  case sequencing_normal { refine IncLogic.seq_normal_incorrect h_ih_H₁ h_ih_H₂, },
  case iterate_zero { refine IncLogic.iterate_zero_incorrect, },
  case iterate_non_zero {exact IncLogic.star_seq h_ih,},
  case backwards_variant {exact IncLogic.backwards_variant h_ih h_N,},
  case choice_right {exact IncLogic.choice_right_incorrect h_ih,},
  case choice_left {exact IncLogic.choice_left_incorrect h_ih,},
  case error_ok {exact IncLogic.error_ok_incorrect},
  case error_er {exact IncLogic.error_er_incorrect},
  case assume_ok {exact IncLogic.assume_incorrect_ok,},
  case assume_er {exact IncLogic.assume_incorrect_er,},
  case assignment_ok {exact IncLogic.assignment_correct,},
  case assignment_er {exact IncLogic.empty_under_incorrect},
  case non_det_assignment_ok {exact IncLogic.non_det_assignment_incorrect},
  case non_det_assignment_er {exact IncLogic.empty_under_incorrect},
  case constancy {exact IncLogic.constancy h_Hf h_ih,},
  case substitution_1 {exact IncLogic.substitution_1 h_HB h_ih h_He,},
  case substitution_2 {exact IncLogic.substitution_2 h_H₁ h_H₂ h_H₃,},
end

lemma IncorectnessProof.completeness {P Q: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}:
  ([* P *]C[* Q *]ty) → IncorrectnessProof P C Q ty :=
begin
  revert P Q ty,
  induction C with
    x e,
  case IncLoLang.stmt.skip {
    intros P Q ty h,

    cases ty,
    {
      -- seek that Q is (λ _, false)
      have H: Q = λ _, false, {
        by_contra hQ,
        have H₂: ∃ σ, Q σ, {
          by_contra h₂,
          push_neg at h₂,
          apply hQ,
          funext,
          specialize h₂ x,
          exact eq_false_intro h₂,
        },
        cases H₂ with σ hσ, 
        specialize h σ hσ,
        rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
        cases hls,
      },
      rw H,
      exact IncorrectnessProof.unit_er,
    },
    {
      have Hpq: ∀ σ, Q σ → P σ, {
        intros σ hqσ,
        specialize h σ hqσ, 
        rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
        cases hls,
        exact hp,
      },

      exact IncorrectnessProof.consequence Q Q P Q Hpq (by {intro x, exact id,}) (by {exact IncorrectnessProof.unit_ok,}),
    },
  },
  case IncLoLang.stmt.assign {
    intros P Q ty h,
    cases ty,
    {
      -- seek that Q is (λ _, false)
      have H: Q = λ _, false, {
        by_contra hQ,
        have H₂: ∃ σ, Q σ, {
          by_contra h₂,
          push_neg at h₂,
          apply hQ,
          funext y,
          specialize h₂ y,
          exact eq_false_intro h₂,
        },
        cases H₂ with σ hσ, 
        specialize h σ hσ,
        rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
        cases hls,
      },
      rw H,
      exact IncorrectnessProof.assignment_er,
    },
    {
      sorry,
      -- have Hpq: ∀ σ, Q σ → P σ, {
      --   intros σ hqσ,
      --   specialize h σ hqσ, 
      --   rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
      --   cases hls,
      --   exact hp,
      -- },

      -- exact IncorrectnessProof.consequence Q Q P Q Hpq (by {intro x, exact id,}) (by {exact IncorrectnessProof.unit_ok,}),
    },
  },
  case IncLoLang.stmt.non_det_assign {
    sorry,
  },
  case IncLoLang.stmt.seq {
    sorry,
  },
  case IncLoLang.stmt.choice {
    sorry,
  },
  case IncLoLang.stmt.star {
    sorry,
  },
  case IncLoLang.stmt.error {
    intros P Q ty h,
    cases ty,
    {
      have Hpq: ∀ σ, Q σ → P σ, {
        intros σ hqσ,
        specialize h σ hqσ, 
        rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
        cases hls,
        exact hp,
      },

      exact IncorrectnessProof.consequence Q Q P Q Hpq (by {intro x, exact id,}) (by {exact IncorrectnessProof.error_er,}),
    },
    {
      -- seek that Q is (λ _, false)
      have H: Q = λ _, false, {
        by_contra hQ,
        have H₂: ∃ σ, Q σ, {
          by_contra h₂,
          push_neg at h₂,
          apply hQ,
          funext,
          specialize h₂ x,
          exact eq_false_intro h₂,
        },
        cases H₂ with σ hσ, 
        specialize h σ hσ,
        rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
        cases hls,
      },
      rw H,
      exact IncorrectnessProof.error_ok,
    },
  },
  case IncLoLang.stmt.assumes {
    intros P Q ty h,

    cases ty,
    {
      -- seek that Q is (λ _, false)
      have H: Q = λ _, false, {
        by_contra hQ,
        have H₂: ∃ σ, Q σ, {
          by_contra h₂,
          push_neg at h₂,
          apply hQ,
          funext,
          specialize h₂ x,
          exact eq_false_intro h₂,
        },
        cases H₂ with σ hσ, 
        specialize h σ hσ,
        rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
        cases hls,
      },
      rw H,
      exact IncorrectnessProof.assume_er,
    },
    {
      have Hpq: ∀ σ, Q σ → P σ ∧ C σ, {
        intros σ hqσ,
        specialize h σ hqσ, 
        rcases h with ⟨σ', ⟨ hp, hls ⟩⟩,
        cases hls,
        exact ⟨hp, hls_h⟩,
      },

      exact IncorrectnessProof.consequence P (λ σ, P σ ∧ C σ) P Q (by {intro x, exact id,}) Hpq IncorrectnessProof.assume_ok,
    },
  },
end

end IncorrectnessCompleteness