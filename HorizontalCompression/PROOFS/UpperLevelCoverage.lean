import HorizontalCompression
import PROOFS.GeneralLemmata

set_option linter.unusedSimpArgs false

/- Proofs: Coverage (Upper Level) -/

namespace COVERAGE.UP.T0H
  /- Lemma: Collapse stops at the Top Formulas -/
  theorem Not_Above_T0H {NODE : Vertex} {DLDS : Graph} :
    ( type0_hypothesis (get_rule NODE DLDS) ) →
    ---------------------------
    ( get_rule.incoming NODE DLDS = [] ) := by
  intro prop_type;
  simp only [get_rule] at prop_type;
  simp only [type0_hypothesis] at prop_type;
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro prop_incoming _ =>
  exact prop_incoming;
end COVERAGE.UP.T0H

namespace COVERAGE.UP.T0E
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T0E {U0 U1 : Vertex} {DLDS : Graph} :
    ( type0_elimination (get_rule U0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( ¬type2_elimination (get_rule U1 DLDS) )
  ∧ ( ¬type2_introduction (get_rule U1 DLDS) )
  ∧ ( ¬type2_hypothesis (get_rule U1 DLDS) ) := by
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type0_elimination] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  --
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Startᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Left_T0E {U0 V0 U1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( type0_elimination (get_rule U0 DLDS) ) →
    ( V0.NUMBER > 0 ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( U1.LEVEL = U0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule U1 DLDS) → type2_elimination (get_rule U1 CLPS) )
  ∧ ( type0_introduction (get_rule U1 DLDS) → type2_introduction (get_rule U1 CLPS) )
  ∧ ( type0_hypothesis (get_rule U1 DLDS) → type2_hypothesis (get_rule U1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type0_elimination] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro  prop_nbrᵥ₀;
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Endᵤ : edge.END = U0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.LEVEL = U0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵤ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Startᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵤ₁; );              /- := RULE.CENTER.NUMBER > 0 -/
                       apply And.intro ( by exact prop_lvlᵤ₁; );              /- := RULE.CENTER.LEVEL > 0 -/
                       apply And.intro ( by exact prop_hptᵤ₁; );              /- := RULE.CENTER.HYPOTHESIS = false -/
                       apply And.intro ( by exact prop_colᵤ₁; );              /- := RULE.CENTER.COLLAPSED = false -/
                       apply And.intro ( by exact prop_pstᵤ₁; );              /- := RULE.CENTER.PAST = [] -/
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro (U0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵤ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵤ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵤ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵤ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );     /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                              /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵤ₁; );
                       apply And.intro ( by exact prop_lvlᵤ₁; );
                       apply And.intro ( by exact prop_hptᵤ₁; );
                       apply And.intro ( by exact prop_colᵤ₁; );
                       apply And.intro ( by exact prop_pstᵤ₁; );
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro (U0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵤ₁;                       /- := consequent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵤ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_fmlᵤ₁; );                               /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );     /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                              /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵤ₁; );
  apply And.intro ( by exact prop_lvlᵤ₁; );
  apply And.intro ( by exact prop_hptᵤ₁; );
  apply And.intro ( by exact prop_colᵤ₁; );
  apply And.intro ( by exact prop_pstᵤ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro out_nbrᵤ₀;                          /- := anc_nbr -/
  apply Exists.intro (U0.LEVEL - 1);                     /- := anc_lvl -/
  apply Exists.intro U0.FORMULA;                         /- := out_fml -/
  apply Exists.intro out_fmlᵤ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro U0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro [];                                 /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_out_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
  apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );     /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by rewrite [prop_pstᵤ₀];                              /- := check_numbers (past::pasts) -/
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );   /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵤ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.indirect, prop_hptᵤ₀];
                       simp only [pre_collapse.indirect.create];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [get_rule.direct.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Right_T0E {U0 V0 V1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( U0.LEVEL = V0.LEVEL ) → ( U0.FORMULA = V0.FORMULA ) →
    ( U0.NUMBER > 0 ) → ( check_numbers (U0.NUMBER::U0.PAST) ) →
    ( type0_elimination (get_rule V0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing V1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming V0 DLDS ) ) →
    ------------------------------------------------------
    ( V1.LEVEL = V0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule V1 DLDS) → type2_elimination (get_rule V1 CLPS) )
  ∧ ( type0_introduction (get_rule V1 DLDS) → type2_introduction (get_rule V1 CLPS) )
  ∧ ( type0_hypothesis (get_rule V1 DLDS) → type2_hypothesis (get_rule V1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_eq_lvl prop_eq_fml;
  --
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  --
  intro prop_typeᵥ₀;
  simp only [get_rule] at prop_typeᵥ₀;
  simp only [type0_elimination] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  --
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵥ : edge.START = V1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Endᵥ : edge.END = V0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.LEVEL = V0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵥ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Startᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro (V0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵥ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵥ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵥ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵥ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );   /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                  /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro (V0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵥ₁;                       /- := consequent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵥ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_fmlᵥ₁; );                                        /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );   /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                  /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [get_rule] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵥ₁; );
  apply And.intro ( by exact prop_lvlᵥ₁; );
  apply And.intro ( by exact prop_hptᵥ₁; );
  apply And.intro ( by exact prop_colᵥ₁; );
  apply And.intro ( by exact prop_pstᵥ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro out_nbrᵥ₀;                          /- := anc_nbr -/
  apply Exists.intro (V0.LEVEL - 1);                     /- := anc_lvl -/
  apply Exists.intro V0.FORMULA;                         /- := out_fml -/
  apply Exists.intro out_fmlᵥ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro V0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro [];                                 /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_out_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
  apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );   /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                  /- := check_numbers (past::pasts) -/
                       apply And.intro ( by simp only [ne_eq];
                                            simp only [List.cons_ne_nil];
                                            trivial; );
                       cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );            /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵥ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.indirect, prop_hptᵥ₀];
                       simp only [pre_collapse.indirect.create];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [get_rule.direct.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T0E

namespace COVERAGE.UP.T0I
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T0I {U0 U1 : Vertex} {DLDS : Graph} :
    ( type0_introduction (get_rule U0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( ¬type2_elimination (get_rule U1 DLDS) )
  ∧ ( ¬type2_introduction (get_rule U1 DLDS) )
  ∧ ( ¬type2_hypothesis (get_rule U1 DLDS) ) := by
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type0_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  --
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Startᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Left_T0I {U0 V0 U1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( type0_introduction (get_rule U0 DLDS) ) →
    ( V0.NUMBER > 0 ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( U1.LEVEL = U0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule U1 DLDS) → type2_elimination (get_rule U1 CLPS) )
  ∧ ( type0_introduction (get_rule U1 DLDS) → type2_introduction (get_rule U1 CLPS) )
  ∧ ( type0_hypothesis (get_rule U1 DLDS) → type2_hypothesis (get_rule U1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type0_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro  prop_nbrᵥ₀;
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Endᵤ : edge.END = U0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.LEVEL = U0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵤ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Startᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵤ₁; );              /- := RULE.CENTER.NUMBER > 0 -/
                       apply And.intro ( by exact prop_lvlᵤ₁; );              /- := RULE.CENTER.LEVEL > 0 -/
                       apply And.intro ( by exact prop_hptᵤ₁; );              /- := RULE.CENTER.HYPOTHESIS = false -/
                       apply And.intro ( by exact prop_colᵤ₁; );              /- := RULE.CENTER.COLLAPSED = false -/
                       apply And.intro ( by exact prop_pstᵤ₁; );              /- := RULE.CENTER.PAST = [] -/
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro (U0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵤ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵤ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵤ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵤ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );     /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                              /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵤ₁; );
                       apply And.intro ( by exact prop_lvlᵤ₁; );
                       apply And.intro ( by exact prop_hptᵤ₁; );
                       apply And.intro ( by exact prop_colᵤ₁; );
                       apply And.intro ( by exact prop_pstᵤ₁; );
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro (U0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵤ₁;                       /- := consequent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵤ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_fmlᵤ₁; );                               /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );     /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                              /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵤ₁; );
  apply And.intro ( by exact prop_lvlᵤ₁; );
  apply And.intro ( by exact prop_hptᵤ₁; );
  apply And.intro ( by exact prop_colᵤ₁; );
  apply And.intro ( by exact prop_pstᵤ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro out_nbrᵤ₀;                          /- := anc_nbr -/
  apply Exists.intro (U0.LEVEL - 1);                     /- := anc_lvl -/
  apply Exists.intro U0.FORMULA;                         /- := out_fml -/
  apply Exists.intro out_fmlᵤ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro U0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro [];                                 /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_out_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
  apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );     /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by rewrite [prop_pstᵤ₀];                              /- := check_numbers (past::pasts) -/
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );   /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵤ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.indirect, prop_hptᵤ₀];
                       simp only [pre_collapse.indirect.create];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Right_T0I {U0 V0 V1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( U0.LEVEL = V0.LEVEL ) → ( U0.FORMULA = V0.FORMULA ) →
    ( U0.NUMBER > 0 ) → ( check_numbers (U0.NUMBER::U0.PAST) ) →
    ( type0_introduction (get_rule V0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing V1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming V0 DLDS ) ) →
    ------------------------------------------------------
    ( V1.LEVEL = V0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule V1 DLDS) → type2_elimination (get_rule V1 CLPS) )
  ∧ ( type0_introduction (get_rule V1 DLDS) → type2_introduction (get_rule V1 CLPS) )
  ∧ ( type0_hypothesis (get_rule V1 DLDS) → type2_hypothesis (get_rule V1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_eq_lvl prop_eq_fml;
  --
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  --
  intro prop_typeᵥ₀;
  simp only [get_rule] at prop_typeᵥ₀;
  simp only [type0_introduction] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro consequentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  --
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵥ : edge.START = V1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Endᵥ : edge.END = V0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.LEVEL = V0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵥ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Startᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro (V0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵥ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵥ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵥ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵥ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );   /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                  /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro out_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro (V0.LEVEL - 1);                     /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵥ₁;                       /- := consequent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro out_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵥ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro [];                                 /- := colours -/
                       apply And.intro ( by exact prop_fmlᵥ₁; );                                        /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_out_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );   /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                  /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.create];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [get_rule] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵥ₁; );
  apply And.intro ( by exact prop_lvlᵥ₁; );
  apply And.intro ( by exact prop_hptᵥ₁; );
  apply And.intro ( by exact prop_colᵥ₁; );
  apply And.intro ( by exact prop_pstᵥ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro out_nbrᵥ₀;                          /- := anc_nbr -/
  apply Exists.intro (V0.LEVEL - 1);                     /- := anc_lvl -/
  apply Exists.intro V0.FORMULA;                         /- := out_fml -/
  apply Exists.intro out_fmlᵥ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro V0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro [];                                 /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_out_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
  apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );   /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                  /- := check_numbers (past::pasts) -/
                       apply And.intro ( by simp only [ne_eq];
                                            simp only [List.cons_ne_nil];
                                            trivial; );
                       cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );            /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵥ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.indirect, prop_hptᵥ₀];
                       simp only [pre_collapse.indirect.create];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T0I


namespace COVERAGE.UP.T2H
  /- Lemma: Collapse stops at the Top Formulas -/
  theorem Not_Above_T2H {NODE : Vertex} {DLDS : Graph} :
    ( type2_hypothesis (get_rule NODE DLDS) ) →
    ---------------------------
    ( get_rule.incoming NODE DLDS = [] ) := by
  intro prop_type;
  simp only [get_rule] at prop_type;
  simp only [type2_hypothesis] at prop_type;
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro prop_incoming _ =>
  exact prop_incoming;
end COVERAGE.UP.T2H

namespace COVERAGE.UP.T2E
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T2E {U0 U1 : Vertex} {DLDS : Graph} :
    ( type2_elimination (get_rule U0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( ¬type2_elimination (get_rule U1 DLDS) )
  ∧ ( ¬type2_introduction (get_rule U1 DLDS) )
  ∧ ( ¬type2_hypothesis (get_rule U1 DLDS) ) := by
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type2_elimination] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  --
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Startᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Left_T2E {U0 V0 U1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( type2_elimination (get_rule U0 DLDS) ) →
    ( V0.NUMBER > 0 ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( U1.LEVEL = U0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule U1 DLDS) → type2_elimination (get_rule U1 CLPS) )
  ∧ ( type0_introduction (get_rule U1 DLDS) → type2_introduction (get_rule U1 CLPS) )
  ∧ ( type0_hypothesis (get_rule U1 DLDS) → type2_hypothesis (get_rule U1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type2_elimination] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro  prop_nbrᵥ₀;
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Endᵤ : edge.END = U0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.LEVEL = U0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵤ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Startᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵤ₁; );              /- := RULE.CENTER.NUMBER > 0 -/
                       apply And.intro ( by exact prop_lvlᵤ₁; );              /- := RULE.CENTER.LEVEL > 0 -/
                       apply And.intro ( by exact prop_hptᵤ₁; );              /- := RULE.CENTER.HYPOTHESIS = false -/
                       apply And.intro ( by exact prop_colᵤ₁; );              /- := RULE.CENTER.COLLAPSED = false -/
                       apply And.intro ( by exact prop_pstᵤ₁; );              /- := RULE.CENTER.PAST = [] -/
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵤ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵤ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵤ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵤ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵤ₀ :: coloursᵤ₀);            /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );                    /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                                             /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_coloursᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵤ₁; );
                       apply And.intro ( by exact prop_lvlᵤ₁; );
                       apply And.intro ( by exact prop_hptᵤ₁; );
                       apply And.intro ( by exact prop_colᵤ₁; );
                       apply And.intro ( by exact prop_pstᵤ₁; );
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵤ₁;                       /- := consequent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵤ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵤ₀ :: coloursᵤ₀);            /- := colours -/
                       apply And.intro ( by exact prop_fmlᵤ₁; );                               /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );                    /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                                             /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_coloursᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵤ₁; );
  apply And.intro ( by exact prop_lvlᵤ₁; );
  apply And.intro ( by exact prop_hptᵤ₁; );
  apply And.intro ( by exact prop_colᵤ₁; );
  apply And.intro ( by exact prop_pstᵤ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro anc_nbrᵤ₀;                          /- := anc_nbr -/
  apply Exists.intro anc_lvlᵤ₀;                          /- := anc_lvl -/
  apply Exists.intro U0.FORMULA;                         /- := out_fml -/
  apply Exists.intro anc_fmlᵤ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro U0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro (colourᵤ₀ :: coloursᵤ₀);            /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_anc_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       rewrite [←prop_anc_lvlᵤ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );                    /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by rewrite [prop_pstᵤ₀];                                             /- := check_numbers (past::pasts) -/
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_coloursᵤ₀; );   /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵤ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.indirect, prop_hptᵤ₀];
                       simp only [pre_collapse.indirect.move_up];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [get_rule.direct.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Right_T2E {U0 V0 V1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( U0.LEVEL = V0.LEVEL ) → ( U0.FORMULA = V0.FORMULA ) →
    ( U0.NUMBER > 0 ) → ( check_numbers (U0.NUMBER::U0.PAST) ) →
    ( type2_elimination (get_rule V0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing V1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming V0 DLDS ) ) →
    ------------------------------------------------------
    ( V1.LEVEL = V0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule V1 DLDS) → type2_elimination (get_rule V1 CLPS) )
  ∧ ( type0_introduction (get_rule V1 DLDS) → type2_introduction (get_rule V1 CLPS) )
  ∧ ( type0_hypothesis (get_rule V1 DLDS) → type2_hypothesis (get_rule V1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_eq_lvl prop_eq_fml;
  --
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  --
  intro prop_typeᵥ₀;
  simp only [get_rule] at prop_typeᵥ₀;
  simp only [type2_elimination] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro colourᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro coloursᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colourᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_coloursᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  --
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵥ : edge.START = V1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Endᵥ : edge.END = V0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.LEVEL = V0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵥ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Startᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵥ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵥ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵥ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵥ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵥ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵥ₀ :: coloursᵥ₀);            /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );                  /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                                 /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_coloursᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵥ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵥ₁;                       /- := consequent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵥ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵥ₀ :: coloursᵥ₀);            /- := colours -/
                       apply And.intro ( by exact prop_fmlᵥ₁; );                                        /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );                  /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                                 /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_coloursᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [get_rule.direct.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [get_rule] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵥ₁; );
  apply And.intro ( by exact prop_lvlᵥ₁; );
  apply And.intro ( by exact prop_hptᵥ₁; );
  apply And.intro ( by exact prop_colᵥ₁; );
  apply And.intro ( by exact prop_pstᵥ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro anc_nbrᵥ₀;                          /- := anc_nbr -/
  apply Exists.intro anc_lvlᵥ₀;                          /- := anc_lvl -/
  apply Exists.intro V0.FORMULA;                         /- := out_fml -/
  apply Exists.intro anc_fmlᵥ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro V0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro (colourᵥ₀ :: coloursᵥ₀);            /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_anc_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       rewrite [←prop_anc_lvlᵥ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );                  /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                                 /- := check_numbers (past::pasts) -/
                       apply And.intro ( by simp only [ne_eq];
                                            simp only [List.cons_ne_nil];
                                            trivial; );
                       cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_coloursᵥ₀; );            /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵥ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.indirect, prop_hptᵥ₀];
                       simp only [pre_collapse.indirect.move_up];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [get_rule.direct.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T2E

namespace COVERAGE.UP.T2I
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T2I {U0 U1 : Vertex} {DLDS : Graph} :
    ( type2_introduction (get_rule U0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( ¬type2_elimination (get_rule U1 DLDS) )
  ∧ ( ¬type2_introduction (get_rule U1 DLDS) )
  ∧ ( ¬type2_hypothesis (get_rule U1 DLDS) ) := by
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type2_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  --
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Startᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Left_T2I {U0 V0 U1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( type2_introduction (get_rule U0 DLDS) ) →
    ( V0.NUMBER > 0 ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( U1.LEVEL = U0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule U1 DLDS) → type2_elimination (get_rule U1 CLPS) )
  ∧ ( type0_introduction (get_rule U1 DLDS) → type2_introduction (get_rule U1 CLPS) )
  ∧ ( type0_hypothesis (get_rule U1 DLDS) → type2_hypothesis (get_rule U1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type2_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colourᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  --
  intro  prop_nbrᵥ₀;
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Endᵤ : edge.END = U0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.LEVEL = U0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵤ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Startᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵤ₁; );              /- := RULE.CENTER.NUMBER > 0 -/
                       apply And.intro ( by exact prop_lvlᵤ₁; );              /- := RULE.CENTER.LEVEL > 0 -/
                       apply And.intro ( by exact prop_hptᵤ₁; );              /- := RULE.CENTER.HYPOTHESIS = false -/
                       apply And.intro ( by exact prop_colᵤ₁; );              /- := RULE.CENTER.COLLAPSED = false -/
                       apply And.intro ( by exact prop_pstᵤ₁; );              /- := RULE.CENTER.PAST = [] -/
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵤ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵤ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵤ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵤ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵤ₀ :: coloursᵤ₀);            /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );                    /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                                             /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_coloursᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵤ₁; );
                       apply And.intro ( by exact prop_lvlᵤ₁; );
                       apply And.intro ( by exact prop_hptᵤ₁; );
                       apply And.intro ( by exact prop_colᵤ₁; );
                       apply And.intro ( by exact prop_pstᵤ₁; );
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵤ₁;                       /- := consequent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵤ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro U0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵤ₀ :: coloursᵤ₀);            /- := colours -/
                       apply And.intro ( by exact prop_fmlᵤ₁; );                               /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );                    /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by rewrite [prop_pstᵤ₀];                                             /- := check_numbers (past::pasts) -/
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_coloursᵤ₀; );   /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵤ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵤ₁; );
  apply And.intro ( by exact prop_lvlᵤ₁; );
  apply And.intro ( by exact prop_hptᵤ₁; );
  apply And.intro ( by exact prop_colᵤ₁; );
  apply And.intro ( by exact prop_pstᵤ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro anc_nbrᵤ₀;                          /- := anc_nbr -/
  apply Exists.intro anc_lvlᵤ₀;                          /- := anc_lvl -/
  apply Exists.intro U0.FORMULA;                         /- := out_fml -/
  apply Exists.intro anc_fmlᵤ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro U0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro (colourᵤ₀ :: coloursᵤ₀);            /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_anc_nbrᵤ₀; );                           /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];                         /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       rewrite [←prop_anc_lvlᵤ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.head (V0.NUMBER :: U0.PAST); );                    /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by rewrite [prop_pstᵤ₀];                                             /- := check_numbers (past::pasts) -/
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_coloursᵤ₀; );   /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵤ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.indirect, prop_hptᵤ₀];
                       simp only [pre_collapse.indirect.move_up];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  /- Indirect Edges -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Right_T2I {U0 V0 V1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( U0.LEVEL = V0.LEVEL ) → ( U0.FORMULA = V0.FORMULA ) →
    ( U0.NUMBER > 0 ) → ( check_numbers (U0.NUMBER::U0.PAST) ) →
    ( type2_introduction (get_rule V0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing V1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming V0 DLDS ) ) →
    ------------------------------------------------------
    ( V1.LEVEL = V0.LEVEL + 1 )
  ∧ ( type0_elimination (get_rule V1 DLDS) → type2_elimination (get_rule V1 CLPS) )
  ∧ ( type0_introduction (get_rule V1 DLDS) → type2_introduction (get_rule V1 CLPS) )
  ∧ ( type0_hypothesis (get_rule V1 DLDS) → type2_hypothesis (get_rule V1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_eq_lvl prop_eq_fml;
  --
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  --
  intro prop_typeᵥ₀;
  simp only [get_rule] at prop_typeᵥ₀;
  simp only [type2_introduction] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro consequentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro colourᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro coloursᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colourᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_coloursᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  --
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵥ : edge.START = V1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Endᵥ : edge.END = V0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.LEVEL = V0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by exact Prop_Upper_LVLᵥ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Startᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵥ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵥ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵥ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵥ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵥ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵥ₀ :: coloursᵥ₀);            /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );                  /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                                 /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_coloursᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [get_rule] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵥ₁; );
                       apply And.intro ( by exact prop_lvlᵥ₁; );
                       apply And.intro ( by exact prop_hptᵥ₁; );
                       apply And.intro ( by exact prop_colᵥ₁; );
                       apply And.intro ( by exact prop_pstᵥ₁; );
                       apply Exists.intro inc_nbrᵥ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵥ₀;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵥ₀;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵥ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵥ₁;                       /- := consequent -/
                       apply Exists.intro V0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵥ₀;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵥ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro V0.NUMBER;                          /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro (colourᵥ₀ :: coloursᵥ₀);            /- := colours -/
                       apply And.intro ( by exact prop_fmlᵥ₁; );                                        /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵥ₁; );                                    /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );                  /- := colour ∈ (out_nbr::past::pasts) -/
                       apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                                 /- := check_numbers (past::pasts) -/
                                            apply And.intro ( by simp only [ne_eq];
                                                                 simp only [List.cons_ne_nil];
                                                                 trivial; );
                                            cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_coloursᵥ₀; );            /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵥ₁; );
                       /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.indirect, prop_hptᵥ₀];
                                            simp only [pre_collapse.indirect.move_up];
                                            rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [get_rule] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_lvlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵥ₁; );
  apply And.intro ( by exact prop_lvlᵥ₁; );
  apply And.intro ( by exact prop_hptᵥ₁; );
  apply And.intro ( by exact prop_colᵥ₁; );
  apply And.intro ( by exact prop_pstᵥ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro anc_nbrᵥ₀;                          /- := anc_nbr -/
  apply Exists.intro anc_lvlᵥ₀;                          /- := anc_lvl -/
  apply Exists.intro V0.FORMULA;                         /- := out_fml -/
  apply Exists.intro anc_fmlᵥ₀;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro V0.NUMBER;                          /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro (colourᵥ₀ :: coloursᵥ₀);            /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                                        /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_anc_nbrᵥ₀; );                                    /- := anc_nbr > 0 -/
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];                                  /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       rewrite [←prop_anc_lvlᵥ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.tail U0.NUMBER (List.Mem.head U0.PAST); );                  /- := colour ∈ (out_nbr::past::pasts) -/
  apply And.intro ( by simp only [check_numbers] at prop_pstᵤ₀ ⊢;                                 /- := check_numbers (past::pasts) -/
                       apply And.intro ( by simp only [ne_eq];
                                            simp only [List.cons_ne_nil];
                                            trivial; );
                       cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.NUMBER mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_coloursᵥ₀; );            /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵥ₁; );
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.indirect, prop_hptᵥ₀];
                       simp only [pre_collapse.indirect.move_up];
                       rewrite [←Prop_Edge_Startᵥ, ←Prop_Edge_Endᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [get_rule.direct.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T2I


namespace COVERAGE.UP.T1X
  /- Lemma: Restrictions on Nodes -/ --666
  theorem Is_Collapse_T1X {NODE : Vertex} {DLDS : Graph} :
    ( type1_collapse (get_rule NODE DLDS) ) →
    ------------------------------------------------------
    ( NODE.COLLAPSED = true ) := by
  intro prop_type₀;
  simp only [get_rule] at prop_type₀;
  simp only [type1_collapse] at prop_type₀;
  cases prop_type₀ with | intro prop_nbr₀ prop_type₀ =>
  cases prop_type₀ with | intro prop_lvl₀ prop_type₀ =>
  cases prop_type₀ with | intro prop_col₀ prop_type₀ =>
  exact prop_col₀;

  /- Lemma: Restrictions on Nodes -/ --666
  theorem Not_Collapse_Not_T1X {NODE : Vertex} {DLDS : Graph} :
    ( NODE.COLLAPSED = false ) →
    ------------------------------------------------------
    ( ¬type1_collapse (get_rule NODE DLDS) ) := by
  intro prop_col_false;
  have Contradiction := ne_true_of_eq_false prop_col_false;
  simp only [get_rule];
  simp only [type1_collapse];
  repeat ( first | rewrite [not_and] | intro _ | contradiction );

  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T1X {U0 U1 : Vertex} {DLDS : Graph} :
    ( type1_collapse (get_rule U0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( ¬type0_elimination (get_rule U1 DLDS) )
  ∧ ( ¬type0_introduction (get_rule U1 DLDS) )
  ∧ ( ¬type0_hypothesis (get_rule U1 DLDS) ) := by
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type1_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  --
  simp only [type_incoming] at prop_incomingᵤ₀;
  have Prop_Inc_Indᵤ₀ := prop_incomingᵤ₀ prop_mem_incomingᵤ₀;
  simp only [type_incoming.check] at Prop_Inc_Indᵤ₀;
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Startᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Endᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Colourᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Colourᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Coloursᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Ancᵤ₀ Prop_Inc_Ind_Duoᵤ₀ =>
  --
  rewrite [Prop_Edge_Startᵤ] at Prop_Inc_Ind_Duoᵤ₀;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₁₃ Prop_Inc_Ind_Duoᵤ₀;
  /- ¬type0_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp +decide; --999 exact List.not_mem_nil _;

  /- Lemma: Upper Nodes Unaffected by Further Collapses -/
  theorem Above_Left_T1X {U0 V0 U1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( type1_collapse (get_rule U0 DLDS) ) →
    ( V0.NUMBER > 0 ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( U1.LEVEL = U0.LEVEL + 1 )
  ∧ ( type2_elimination (get_rule U1 DLDS) → type2_elimination (get_rule U1 CLPS) )
  ∧ ( type2_introduction (get_rule U1 DLDS) → type2_introduction (get_rule U1 CLPS) )
  ∧ ( type2_hypothesis (get_rule U1 DLDS) → type2_hypothesis (get_rule U1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type1_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  --
  intro  prop_nbrᵥ₀;
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Endᵤ : edge.END = U0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.LEVEL = U0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵤ];
                                                       cases prop_incomingᵤ₀ prop_mem_incomingᵤ₀ with | intro Prop_Startᵤ₀ _ =>
                                                       cases Prop_Startᵤ₀ with | intro _ Prop_Startᵤ₀ =>
                                                       cases Prop_Startᵤ₀ with | intro Prop_Start_LVLᵤ₀ _ =>
                                                       simp only [get_rule] at Prop_Start_LVLᵤ₀;
                                                       exact Prop_Start_LVLᵤ₀;
  apply And.intro ( by exact Prop_Upper_LVLᵤ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Collapse prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Startᵤ];
  /- type2_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵤ₁; );              /- := RULE.CENTER.NUMBER > 0 -/
                       apply And.intro ( by exact prop_lvlᵤ₁; );              /- := RULE.CENTER.LEVEL > 0 -/
                       apply And.intro ( by exact prop_hptᵤ₁; );              /- := RULE.CENTER.HYPOTHESIS = false -/
                       apply And.intro ( by exact prop_colᵤ₁; );              /- := RULE.CENTER.COLLAPSED = false -/
                       apply And.intro ( by exact prop_pstᵤ₁; );              /- := RULE.CENTER.PAST = [] -/
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₁;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₁;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₁;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵤ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵤ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵤ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵤ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro colourᵤ₁;                           /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro coloursᵤ₁;                          /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₁; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_lvlᵤ₁; );                           /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       apply And.intro ( by rewrite [←Prop_Edge_Endᵤ];                         /- := colour ∈ (out_nbr::past::pasts) -/
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colourᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.NUMBER :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colourᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.NUMBER prop_colourᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>                    /- := check_numbers (past::pasts) -/
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by exact prop_coloursᵤ₁; );                                              /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_directᵤ₁; );
                       /- Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type2_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵤ₁; );
                       apply And.intro ( by exact prop_lvlᵤ₁; );
                       apply And.intro ( by exact prop_hptᵤ₁; );
                       apply And.intro ( by exact prop_colᵤ₁; );
                       apply And.intro ( by exact prop_pstᵤ₁; );
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₁;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₁;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵤ₁;                       /- := consequent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₁;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵤ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro colourᵤ₁;                           /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro coloursᵤ₁;                          /- := colours -/
                       apply And.intro ( by exact prop_fmlᵤ₁; );                               /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₁; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_lvlᵤ₁; );                           /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       apply And.intro ( by rewrite [←Prop_Edge_Endᵤ];                         /- := colour ∈ (out_nbr::past::pasts) -/
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colourᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.NUMBER :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colourᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.NUMBER prop_colourᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>                    /- := check_numbers (past::pasts) -/
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by exact prop_coloursᵤ₁; );                                              /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_directᵤ₁; );
                       /- Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type2_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro colourᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro coloursᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colourᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_coloursᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵤ₁; );
  apply And.intro ( by exact prop_lvlᵤ₁; );
  apply And.intro ( by exact prop_hptᵤ₁; );
  apply And.intro ( by exact prop_colᵤ₁; );
  apply And.intro ( by exact prop_pstᵤ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro anc_nbrᵤ₁;                          /- := anc_nbr -/
  apply Exists.intro anc_lvlᵤ₁;                          /- := anc_lvl -/
  apply Exists.intro U0.FORMULA;                         /- := out_fml -/
  apply Exists.intro anc_fmlᵤ₁;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro colourᵤ₁;                           /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro coloursᵤ₁;                          /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_anc_nbrᵤ₁; );                           /- := anc_nbr > 0 -/
  apply And.intro ( by exact prop_anc_lvlᵤ₁; );                           /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
  apply And.intro ( by rewrite [←Prop_Edge_Endᵤ];                         /- := colour ∈ (out_nbr::past::pasts) -/
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                  cases prop_colourᵤ₁ with
                                                                  | head => exact List.Mem.head (V0.NUMBER :: pastᵤ₁ :: pastsᵤ₁);
                                                                  | tail _ prop_colourᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                ( List.Mem.tail V0.NUMBER prop_colourᵤ₁ );
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>                    /- := check_numbers (past::pasts) -/
                       cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                       cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                       rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
  apply And.intro ( by exact prop_coloursᵤ₁; );                                              /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵤ₁; );
  /- Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_directᵤ₁; );
  /- Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵤ₁;
end COVERAGE.UP.T1X


namespace COVERAGE.UP.T3X
  /- Lemma: Restrictions on Nodes -/ --666
  theorem Is_Collapse_T3X {NODE : Vertex} {DLDS : Graph} :
    ( type3_collapse (get_rule NODE DLDS) ) →
    ------------------------------------------------------
    ( NODE.COLLAPSED = true ) := by
  intro prop_type₀;
  simp only [get_rule] at prop_type₀;
  simp only [type3_collapse] at prop_type₀;
  cases prop_type₀ with | intro prop_nbr₀ prop_type₀ =>
  cases prop_type₀ with | intro prop_lvl₀ prop_type₀ =>
  cases prop_type₀ with | intro prop_col₀ prop_type₀ =>
  exact prop_col₀;

  /- Lemma: Restrictions on Nodes -/ --666
  theorem Not_Collapse_Not_T3X {NODE : Vertex} {DLDS : Graph} :
    ( NODE.COLLAPSED = false ) →
    ------------------------------------------------------
    ( ¬type3_collapse (get_rule NODE DLDS) ) := by
  intro prop_col_false;
  have Contradiction := ne_true_of_eq_false prop_col_false;
  simp only [get_rule];
  simp only [type3_collapse];
  repeat ( first | rewrite [not_and] | intro _ | contradiction );

  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T3X {U0 U1 : Vertex} {DLDS : Graph} :
    ( type3_collapse (get_rule U0 DLDS) ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( ¬type0_elimination (get_rule U1 DLDS) )
  ∧ ( ¬type0_introduction (get_rule U1 DLDS) )
  ∧ ( ¬type0_hypothesis (get_rule U1 DLDS) ) := by
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type3_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  --
  simp only [type_incoming] at prop_incomingᵤ₀;
  have Prop_Inc_Indᵤ₀ := prop_incomingᵤ₀ prop_mem_incomingᵤ₀;
  simp only [type_incoming.check] at Prop_Inc_Indᵤ₀;
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Startᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Endᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Colourᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Colourᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Coloursᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Ancᵤ₀ Prop_Inc_Ind_Duoᵤ₀ =>
  --
  rewrite [Prop_Edge_Startᵤ] at Prop_Inc_Ind_Duoᵤ₀;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₁₃ Prop_Inc_Ind_Duoᵤ₀;
  /- ¬type0_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp +decide; --999 exact List.not_mem_nil _;

  /- Lemma: Upper Nodes Unaffected by Further Collapses -/
  theorem Above_Left_T3X {U0 V0 U1 : Vertex} {DLDS : Graph} :
    ( CLPS.is_collapse U0 V0 DLDS ) →
    ( type3_collapse (get_rule U0 DLDS) ) →
    ( V0.NUMBER > 0 ) →
    ( ∃(edge : Deduction), ( edge ∈ get_rule.outgoing U1 DLDS )
                         ∧ ( edge ∈ get_rule.incoming U0 DLDS ) ) →
    ------------------------------------------------------
    ( U1.LEVEL = U0.LEVEL + 1 )
  ∧ ( type2_elimination (get_rule U1 DLDS) → type2_elimination (get_rule U1 CLPS) )
  ∧ ( type2_introduction (get_rule U1 DLDS) → type2_introduction (get_rule U1 CLPS) )
  ∧ ( type2_hypothesis (get_rule U1 DLDS) → type2_hypothesis (get_rule U1 CLPS) ) := by
  intro prop_collapse;
  --
  intro prop_typeᵤ₀;
  simp only [get_rule] at prop_typeᵤ₀;
  simp only [type3_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_coloursᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  --
  intro  prop_nbrᵥ₀;
  --
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.LEVEL = U0.LEVEL + 1 -/
  have Prop_Edge_Startᵤ : edge.START = U1 := COLLAPSE.Simp_Start_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Endᵤ : edge.END = U0 := COLLAPSE.Simp_End_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.LEVEL = U0.LEVEL + 1 := by rewrite [←Prop_Edge_Startᵤ];
                                                       cases prop_incomingᵤ₀ prop_mem_incomingᵤ₀ with | intro Prop_Startᵤ₀ _ =>
                                                       cases Prop_Startᵤ₀ with | intro _ Prop_Startᵤ₀ =>
                                                       cases Prop_Startᵤ₀ with | intro Prop_Start_LVLᵤ₀ _ =>
                                                       simp only [get_rule] at Prop_Start_LVLᵤ₀;
                                                       exact Prop_Start_LVLᵤ₀;
  apply And.intro ( by exact Prop_Upper_LVLᵤ; );
  /- Unfold "get_rule U1 CLPS" -/
  rewrite [←Prop_Edge_Startᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Collapse prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Startᵤ];
  /- type2_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_elimination];
                       apply And.intro ( by exact prop_nbrᵤ₁; );              /- := RULE.CENTER.NUMBER > 0 -/
                       apply And.intro ( by exact prop_lvlᵤ₁; );              /- := RULE.CENTER.LEVEL > 0 -/
                       apply And.intro ( by exact prop_hptᵤ₁; );              /- := RULE.CENTER.HYPOTHESIS = false -/
                       apply And.intro ( by exact prop_colᵤ₁; );              /- := RULE.CENTER.COLLAPSED = false -/
                       apply And.intro ( by exact prop_pstᵤ₁; );              /- := RULE.CENTER.PAST = [] -/
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₁;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₁;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₁;                          /- := anc_fml -/
                       apply Exists.intro major_hptᵤ₁;                        /- := major_hpt -/
                       apply Exists.intro minor_hptᵤ₁;                        /- := minor_hpt -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro major_depᵤ₁;                        /- := major_dep -/
                       apply Exists.intro minor_depᵤ₁;                        /- := minor_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro colourᵤ₁;                           /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro coloursᵤ₁;                          /- := colours -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₁; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_lvlᵤ₁; );                           /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       apply And.intro ( by rewrite [←Prop_Edge_Endᵤ];                         /- := colour ∈ (out_nbr::past::pasts) -/
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colourᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.NUMBER :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colourᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.NUMBER prop_colourᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>                    /- := check_numbers (past::pasts) -/
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by exact prop_coloursᵤ₁; );                                              /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_directᵤ₁; );
                       /- Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type2_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [get_rule] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colourᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_coloursᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       --
                       simp only [type2_introduction];
                       apply And.intro ( by exact prop_nbrᵤ₁; );
                       apply And.intro ( by exact prop_lvlᵤ₁; );
                       apply And.intro ( by exact prop_hptᵤ₁; );
                       apply And.intro ( by exact prop_colᵤ₁; );
                       apply And.intro ( by exact prop_pstᵤ₁; );
                       apply Exists.intro inc_nbrᵤ₁;                          /- := inc_nbr -/
                       apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
                       apply Exists.intro anc_nbrᵤ₁;                          /- := anc_nbr -/
                       apply Exists.intro anc_lvlᵤ₁;                          /- := anc_lvl -/
                       apply Exists.intro antecedentᵤ₁;                       /- := antecedent -/
                       apply Exists.intro consequentᵤ₁;                       /- := consequent -/
                       apply Exists.intro U0.FORMULA;                         /- := out_fml -/
                       apply Exists.intro anc_fmlᵤ₁;                          /- := anc_fml -/
                       apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
                       apply Exists.intro inc_depᵤ₁;                          /- := inc_dep -/
                       apply Exists.intro V0.NUMBER;                          /- := past -/
                       apply Exists.intro colourᵤ₁;                           /- := colour -/
                       apply Exists.intro U0.PAST;                            /- := pasts -/
                       apply Exists.intro coloursᵤ₁;                          /- := colours -/
                       apply And.intro ( by exact prop_fmlᵤ₁; );                               /- := RULE.CENTER.FORMULA = antecedent>>consequent -/
                       apply And.intro ( by exact prop_inc_nbrᵤ₁; );                           /- := inc_nbr > 0 -/
                       apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_nbrᵤ₁; );                           /- := anc_nbr > 0 -/
                       apply And.intro ( by exact prop_anc_lvlᵤ₁; );                           /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
                       apply And.intro ( by rewrite [←Prop_Edge_Endᵤ];                         /- := colour ∈ (out_nbr::past::pasts) -/
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colourᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.NUMBER :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colourᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.NUMBER prop_colourᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>                    /- := check_numbers (past::pasts) -/
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by exact prop_coloursᵤ₁; );                                              /- := check_numbers (colour::colours) -/
                       /- Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_incomingᵤ₁; );
                       /- Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
                       apply And.intro ( by exact prop_directᵤ₁; );
                       /- Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
                       exact prop_indirectᵤ₁; );
  /- type2_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [get_rule] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro colourᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro coloursᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colourᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_coloursᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  --
  simp only [type2_hypothesis];
  apply And.intro ( by exact prop_nbrᵤ₁; );
  apply And.intro ( by exact prop_lvlᵤ₁; );
  apply And.intro ( by exact prop_hptᵤ₁; );
  apply And.intro ( by exact prop_colᵤ₁; );
  apply And.intro ( by exact prop_pstᵤ₁; );
  apply Exists.intro U0.NUMBER;                          /- := out_nbr -/
  apply Exists.intro anc_nbrᵤ₁;                          /- := anc_nbr -/
  apply Exists.intro anc_lvlᵤ₁;                          /- := anc_lvl -/
  apply Exists.intro U0.FORMULA;                         /- := out_fml -/
  apply Exists.intro anc_fmlᵤ₁;                          /- := anc_fml -/
  apply Exists.intro (U0.HYPOTHESIS || V0.HYPOTHESIS);   /- := out_hpt -/
  apply Exists.intro V0.NUMBER;                          /- := past -/
  apply Exists.intro colourᵤ₁;                           /- := colour -/
  apply Exists.intro U0.PAST;                            /- := pasts -/
  apply Exists.intro coloursᵤ₁;                          /- := colours -/
  apply And.intro ( by exact prop_nbrᵤ₀; );                               /- := out_nbr > 0 -/
  apply And.intro ( by exact prop_anc_nbrᵤ₁; );                           /- := anc_nbr > 0 -/
  apply And.intro ( by exact prop_anc_lvlᵤ₁; );                           /- := anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL -/
  apply And.intro ( by rewrite [←Prop_Edge_Endᵤ];                         /- := colour ∈ (out_nbr::past::pasts) -/
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                  cases prop_colourᵤ₁ with
                                                                  | head => exact List.Mem.head (V0.NUMBER :: pastᵤ₁ :: pastsᵤ₁);
                                                                  | tail _ prop_colourᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                ( List.Mem.tail V0.NUMBER prop_colourᵤ₁ );
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>                    /- := check_numbers (past::pasts) -/
                       cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                       cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                       rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
  apply And.intro ( by exact prop_coloursᵤ₁; );                                              /- := check_numbers (colour::colours) -/
  /- Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_incomingᵤ₁; );
  /- Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Startᵤ, ←Prop_Edge_Endᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by exact prop_directᵤ₁; );
  /- Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  exact prop_indirectᵤ₁;
end COVERAGE.UP.T3X

/- End -/
