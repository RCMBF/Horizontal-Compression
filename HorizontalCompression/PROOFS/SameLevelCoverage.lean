import HorizontalCompression
import PROOFS.GeneralLemmata
import PROOFS.DefineLemmata
import PROOFS.RewriteLemmata

set_option linter.unusedSimpArgs false

/- Proofs: Coverage (Same Level) -/

namespace COVERAGE.T1_Of_T1
  /- Pre-Collapse: Type1 Collapse -/
  theorem Col_Of_PreCollapse_Col {RULE : Neighborhood} :
    ( type1_collapse RULE ) →
    ---------------------------
    ( type1_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type1_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  --
  simp only [pre_collapse];
  simp only [prop_col];
  --
  simp only [type1_collapse];
  apply And.intro ( by exact prop_nbr; );
  apply And.intro ( by exact prop_lvl; );
  apply And.intro ( by exact prop_col; );
  exact prop_type;
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T1_Of_T1

namespace COVERAGE.T3_Of_T3
  /- Pre-Collapse: Type3 Collapse -/
  theorem Col_Of_PreCollapse_Col {RULE : Neighborhood} :
    ( type3_collapse RULE ) →
    ---------------------------
    ( type3_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type3_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  --
  simp only [pre_collapse];
  simp only [prop_col];
  --
  simp only [type3_collapse];
  apply And.intro ( by exact prop_nbr; );
  apply And.intro ( by exact prop_lvl; );
  apply And.intro ( by exact prop_col; );
  exact prop_type;
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T3_Of_T3

namespace COVERAGE.T3_Of_T1
  /- Lemma: Type 3 Pre-Collapse from Type 1 Pre-Collapse -/
  theorem PreCol_Of_Pre {RULE : Neighborhood} :
    ( type1_pre_collapse RULE ) →
    ---------------------------
    ( type3_pre_collapse RULE ) := by
  intro prop_type;
  simp only [type1_pre_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro prop_inc_nil prop_type =>
  cases prop_type with | intro prop_inc_len prop_type =>
  cases prop_type with | intro prop_out_unit prop_type =>
  cases prop_type with | intro prop_out_colours prop_type =>
  cases prop_type with | intro prop_dir_nil prop_type =>
  cases prop_type with | intro prop_ind_starts prop_type =>
  cases prop_type with | intro prop_ind_len prop_type =>
  cases prop_type with | intro prop_ind_colours prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_indirect =>
  --
  simp only [type3_pre_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                         /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                         /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                         /- := RULE.CENTER.COLLAPSED = false -/
  apply And.intro ( by exact prop_pst; );                         /- := RULE.CENTER.PAST = [] -/
  /- Check Deduction Edges -/
  apply And.intro ( by exact prop_inc_nil; );                     /- := ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) -/
  apply And.intro ( by exact prop_inc_len; );                     /- := List.length (RULE.INCOMING) ≤ 2 -/
  apply And.intro ( by exact prop_out_unit; );                    /- := RULE.OUTGOING = [out] -/
  apply And.intro ( by exact prop_out_colours; );                 /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
  /- Check Ancestral Paths -/
  apply And.intro ( by rewrite [prop_dir_nil];                    /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
                       intros; trivial; );
  apply And.intro ( by rewrite [prop_dir_nil];                    /- := RULE.DIRECT ≠ [] → RULE.CENTER.HYPOTHESIS = true -/
                       intros; trivial; );
  apply And.intro ( by exact Or.inl prop_dir_nil; );              /- := ( RULE.DIRECT ≠ [] ) ∨ ( RULE.DIRECT = [dir] ) -/
  apply And.intro ( by exact prop_ind_starts; );                  /- := ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) -/
  apply And.intro ( by exact prop_ind_len; );                     /- := List.length (RULE.INCOMING) = List.length (RULE.INDIRECT) -/
  apply And.intro ( by exact prop_incoming; );                    /- := type_incoming RULE -/
  apply And.intro ( by simp only [type_outgoing₃];                /- := type_outgoing RULE -/
                       intro out out_cases;
                       exact Or.inl (prop_outgoing out_cases); );
  apply And.intro ( by simp only [type_direct];                   /- := type_direct RULE -/
                       rewrite [prop_dir_nil];
                       intro dir dir_cases;
                       trivial; );
  exact prop_indirect;                                            /- := type_indirect RULE -/
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- Lemma: Type 3 Collapse from Type 1 Collapse -/
  theorem Col_Of_Col {RULE : Neighborhood} :
    ( type1_collapse RULE ) →
    ---------------------------
    ( type3_collapse RULE ) := by
  intro prop_type;
  simp only [type1_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro prop_inc_nil prop_type =>
  cases prop_type with | intro prop_out_cons prop_type =>
  cases prop_type with | intro prop_out_colours prop_type =>
  cases prop_type with | intro prop_dir_nil prop_type =>
  cases prop_type with | intro prop_ind_len prop_type =>
  cases prop_type with | intro prop_ind_colours prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_indirect =>
  --
  simp only [type3_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                         /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                         /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                         /- := RULE.CENTER.COLLAPSED = true -/
  apply And.intro ( by exact prop_pst; );                         /- := RULE.CENTER.PAST = (past::pasts) -/
  /- Check Deduction Edges -/
  apply And.intro ( by exact prop_inc_nil; );                     /- := ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
  apply And.intro ( by exact prop_out_cons; );                    /- := RULE.OUTGOING = (out::outs) -/
  apply And.intro ( by exact prop_out_colours; );                 /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
  /- Check Ancestral Paths -/
  apply And.intro ( by rewrite [prop_dir_nil];                    /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
                       intros; trivial; );
  apply And.intro ( by rewrite [prop_dir_nil];                    /- := RULE.DIRECT ≠ [] → RULE.CENTER.HYPOTHESIS = true -/
                       intros; trivial; );
  apply And.intro ( by exact prop_ind_len; );                     /- := List.length (RULE.INCOMING) = List.length (RULE.INDIRECT) -/
  apply And.intro ( by exact prop_incoming; );                    /- := type_incoming RULE -/
  apply And.intro ( by simp only [type_outgoing₃];                /- := type_outgoing RULE -/
                       intro out out_cases;
                       exact Or.inl (prop_outgoing out_cases); );
  apply And.intro ( by simp only [type_direct];                   /- := type_direct RULE -/
                       rewrite [prop_dir_nil];
                       intro dir dir_cases;
                       trivial; );
  exact prop_indirect;                                            /- := type_indirect RULE -/
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T3_Of_T1


namespace COVERAGE.T1_Of_T0
  --333 set_option trace.Meta.Tactic.simp true
  /- Pre-Collapse: Type0 ⊇-Elimination -/
  theorem PreCol_Of_PreCollapse_Elim {RULE : Neighborhood} :
    ( type0_elimination RULE ) →
    ---------------------------
    ( type1_pre_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type0_elimination] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro major_hpt prop_type =>
  cases prop_type with | intro minor_hpt prop_type =>
  cases prop_type with | intro major_dep prop_type =>
  cases prop_type with | intro minor_dep prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.outgoing];
  simp only [pre_collapse.direct];
  simp only [pre_collapse.indirect];
  simp only [pre_collapse.indirect.create];
  simp only [type1_pre_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                   /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                   /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                   /- := RULE.CENTER.COLLAPSED = false -/
  apply And.intro ( by exact prop_pst; );                   /- := RULE.CENTER.PAST = [] -/
  /- Check Deduction Edges -/
  apply And.intro ( by simp only [reduceCtorEq];            /- := ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) -/
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );     /- := List.length (RULE.INCOMING) ≤ 2 -/
  apply And.intro ( by simp only [List.cons.injEq];             /- := RULE.OUTGOING = [out] -/
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;               /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check Ancestral Paths -/
  apply And.intro ( by trivial; );                                      /- := RULE.DIRECT = [] -/
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;               /- := ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) -/
                       apply DEFINE.Def_Check_Path_Starts ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_starts];
                       simp only [DEFINE.check_path_starts.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );                      /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
  apply And.intro ( by intro ind ind_mem;                               /- := ind.COLOURS = [0, RULE.CENTER.NUMBER] -/
                       apply DEFINE.Def_Check_Path_Colours ind_mem;
                       simp only [DEFINE.check_path_colours];
                       trivial; );
  /- Check Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and, and_true];
                                   apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );                                  /- := INC.START.NUMBER > 0 -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro RULE.CENTER.NUMBER;                                                   /- colour (Path Notation) -/
                                   apply Exists.intro [];                                                                   /- colours (Path Notation) -/
                                   apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL - 1) out_fml false false []);        /- anc (Ancestral Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                       | tail _ inc_cases => cases inc_cases with
                                             | head _ => simp only [Vertex.node.injEq, true_and, and_true];
                                                         apply And.intro ( by exact prop_inc_nbr; );                                              /- := INC.START.NUMBER > 0 -/
                                                         /- Match-Verification Loop: -/
                                                         apply Exists.intro RULE.CENTER.NUMBER;                                                   /- colour (Path Notation) -/
                                                         apply Exists.intro [];                                                                   /- colours (Path Notation) -/
                                                         apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL - 1) out_fml false false []);        /- anc (Ancestral Node) -/
                                                         exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                             | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₁];
                       apply Or.inr; simp only [type_outgoing₁.check_ie₁, and_assoc];                  /- := Type 0 Elimination -/
                       cases out_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );                      /- := CENTER.HYPOTHESIS = false ∨ CENTER.COLLAPSED = true -/
                                   apply And.intro ( by exact prop_out_nbr; );                         /- := OUT.END.NUMBER > 0 -/
                                   apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );       /- := OUT.COLOUR ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (node inc_nbr (RULE.CENTER.LEVEL+1) antecedent minor_hpt false []);   /- inc (Incoming Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                       | tail _ out_cases => trivial; );
  /- Check Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Vertex.node.injEq, true_and];
              apply And.intro ( by exact prop_out_nbr; );                                         /- := IND.START.NUMBER > 0 -/
              apply And.intro ( by exact Nat.le_refl (RULE.CENTER.LEVEL - 1); );                  /- := IND.START.LEVEL ≤ RULE.CENTER.LEVEL - 1 -/
              apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );                             /- := IND.END.NUMBER > 0 -/
              apply And.intro ( by simp only [List.length];                                       /- := IND.START.LEVEL + List.length (IND.COLOURS) = RULE.CENTER.LEVEL + 1 -/
                                   simp only [Nat.zero_add, ←Nat.add_assoc];
                                   simp only [Nat.sub_add_cancel prop_lvl]; );
              apply Exists.intro RULE.CENTER.NUMBER;                                              /- colour (Path Notation) -/
              apply Exists.intro [];                                                              /- colours (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbr );                  /- := check_numbers (colour::colours) -/
              apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                       /- := colour ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
              apply And.intro ( by trivial; );                                                    /- := IND.COLOURS = (0::colour::colours) -/
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro #major_dep;                                                              /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge IND.END RULE.CENTER 0 dep_inc ∈ RULE.INCOMING -/
                                   intro inc inc_cases;                                                                       /- := ( INC.START = IND.END ) ↔ ( INC = edge IND.END RULE.CENTER 0 dep_inc ) -/
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Resolve Missmatch: -/
                                   simp only [Deduction.edge.injEq, true_and, and_true];
                                   simp only [Vertex.node.injEq, true_and, and_true];
                                   simp only [iff_self_and, and_imp];
                                   have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                   simp only [ne_eq, eq_comm] at succ_ne_self;
                                   intro succ_eq_self;
                                   trivial; )
                              ( by apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL - 1) out_fml false false []);          /- out (Outgoing Node) -/
                                   apply Exists.intro (minor_dep ∪ major_dep);                                                /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by simp only [Vertex.node.injEq]; );                                     /- := ( colours = [] ) ↔ ( out = IND.START ) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge RULE.CENTER out colour dep_out ∈ RULE.OUTGOING -/
                                   intro out out_cases;                                                                       /- := ( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out ) -/
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial; );
  | tail _ ind_cases => cases ind_cases with
                        | head _ => simp only [Vertex.node.injEq, true_and];
                                    apply And.intro ( by exact prop_out_nbr; );                                         /- := IND.START.NUMBER > 0 -/
                                    apply And.intro ( by exact Nat.le_refl (RULE.CENTER.LEVEL - 1); );                  /- := IND.START.LEVEL ≤ RULE.CENTER.LEVEL - 1 -/
                                    apply And.intro ( by exact prop_inc_nbr; );                                         /- := IND.END.NUMBER > 0 -/
                                    apply And.intro ( by simp only [List.length];                                       /- := IND.START.LEVEL + List.length (IND.COLOURS) = RULE.CENTER.LEVEL + 1 -/
                                                         simp only [Nat.zero_add, ←Nat.add_assoc];
                                                         simp only [Nat.sub_add_cancel prop_lvl]; );
                                    apply Exists.intro RULE.CENTER.NUMBER;                                              /- colour (Path Notation) -/
                                    apply Exists.intro [];                                                              /- colours (Path Notation) -/
                                    apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbr );                  /- := check_numbers (colour::colours) -/
                                    apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                       /- := colour ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                    apply And.intro ( by trivial; );                                                    /- := IND.COLOURS = (0::colour::colours) -/
                                    /- Match-Verification Loop: -/
                                    exact And.intro ( by apply Exists.intro #minor_dep;                                                              /- dep_inc (Incoming Dependency) -/
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge IND.END RULE.CENTER 0 dep_inc ∈ RULE.INCOMING -/
                                                         intro inc inc_cases;                                                                       /- := ( INC.START = IND.END ) ↔ ( INC = edge IND.END RULE.CENTER 0 dep_inc ) -/
                                                         apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                                         simp only [DEFINE.check_path_incoming];
                                                         /- Resolve Missmatch: -/
                                                         simp only [Deduction.edge.injEq, true_and, and_true];
                                                         simp only [Vertex.node.injEq, true_and, and_true];
                                                         simp only [iff_self_and, and_imp];
                                                         have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                                         simp only [ne_eq] at succ_ne_self;
                                                         intro succ_eq_self;
                                                         trivial; )
                                                    ( by apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL - 1) out_fml false false []);          /- out (Outgoing Node) -/
                                                         apply Exists.intro (minor_dep ∪ major_dep);                                                /- dep_out (Outgoing Dependency) -/
                                                         apply And.intro ( by simp only [Vertex.node.injEq]; );                                     /- := ( colours = [] ) ↔ ( out = IND.START ) -/
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge RULE.CENTER out colour dep_out ∈ RULE.OUTGOING -/
                                                         intro out out_cases;                                                                       /- := ( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out ) -/
                                                         apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                                         simp only [DEFINE.check_path_outgoing];
                                                         /- Perfect Match! -/
                                                         trivial; );
                        | tail _ ind_cases => trivial;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Pre-Collapse: Type0 ⊇-Introduction -/
  theorem PreCol_Of_PreCollapse_Intro {RULE : Neighborhood} :
    ( type0_introduction RULE ) →
    ---------------------------
    ( type1_pre_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type0_introduction] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro consequent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro inc_dep prop_type =>
  cases prop_type with | intro prop_fml prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.outgoing];
  simp only [pre_collapse.direct];
  simp only [pre_collapse.indirect];
  simp only [pre_collapse.indirect.create];
  simp only [type1_pre_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                   /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                   /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                   /- := RULE.CENTER.COLLAPSED = false -/
  apply And.intro ( by exact prop_pst; );                   /- := RULE.CENTER.PAST = [] -/
  /- Check Deduction Edges -/
  apply And.intro ( by simp only [reduceCtorEq];            /- := ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) -/
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );     /- := List.length (RULE.INCOMING) ≤ 2 -/
  apply And.intro ( by simp only [List.cons.injEq];             /- := RULE.OUTGOING = [out] -/
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;               /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check Ancestral Paths -/
  apply And.intro ( by trivial; );                                      /- := RULE.DIRECT = [] -/
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;               /- := ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) -/
                       apply DEFINE.Def_Check_Path_Starts ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_starts];
                       simp only [DEFINE.check_path_starts.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );                      /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
  apply And.intro ( by intro ind ind_mem;                               /- := ind.COLOURS = [0, RULE.CENTER.NUMBER] -/
                       apply DEFINE.Def_Check_Path_Colours ind_mem;
                       simp only [DEFINE.check_path_colours];
                       trivial; );
  /- Check Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and, and_true];
                                   apply And.intro ( by exact prop_inc_nbr; );                                              /- := INC.START.NUMBER > 0 -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro RULE.CENTER.NUMBER;                                                   /- colour (Path Notation) -/
                                   apply Exists.intro [];                                                                   /- colours (Path Notation) -/
                                   apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL - 1) out_fml false false []);        /- anc (Ancestral Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                       | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₁];
                       apply Or.inr; simp only [type_outgoing₁.check_ie₁, and_assoc];                  /- := Type 0 Introduction -/
                       cases out_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );                      /- := CENTER.HYPOTHESIS = false ∨ CENTER.COLLAPSED = true -/
                                   apply And.intro ( by exact prop_out_nbr; );                         /- := OUT.END.NUMBER > 0 -/
                                   apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );       /- := OUT.COLOUR ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (node inc_nbr (RULE.CENTER.LEVEL+1) consequent false false []);       /- inc (Incoming Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                       | tail _ out_cases => trivial; );
  /- Check Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Vertex.node.injEq, true_and];
              apply And.intro ( by exact prop_out_nbr; );                                         /- := IND.START.NUMBER > 0 -/
              apply And.intro ( by exact Nat.le_refl (RULE.CENTER.LEVEL - 1); );                  /- := IND.START.LEVEL ≤ RULE.CENTER.LEVEL - 1 -/
              apply And.intro ( by exact prop_inc_nbr; );                                         /- := IND.END.NUMBER > 0 -/
              apply And.intro ( by simp only [List.length];                                       /- := IND.START.LEVEL + List.length (IND.COLOURS) = RULE.CENTER.LEVEL + 1 -/
                                   simp only [Nat.zero_add, ←Nat.add_assoc];
                                   simp only [Nat.sub_add_cancel prop_lvl]; );
              apply Exists.intro RULE.CENTER.NUMBER;                                              /- colour (Path Notation) -/
              apply Exists.intro [];                                                              /- colours (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbr );                  /- := check_numbers (colour::colours) -/
              apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                       /- := colour ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
              apply And.intro ( by trivial; );                                                    /- := IND.COLOURS = (0::colour::colours) -/
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro #inc_dep;                                                               /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge IND.END RULE.CENTER 0 dep_inc ∈ RULE.INCOMING -/
                                   intro inc inc_cases;                                                                       /- := ( INC.START = IND.END ) ↔ ( INC = edge IND.END RULE.CENTER 0 dep_inc ) -/
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Perfect Match! -/
                                   trivial; )
                              ( by apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL - 1) out_fml false false []);          /- out (Outgoing Node) -/
                                   apply Exists.intro (inc_dep − [antecedent]);                                               /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by simp only [Vertex.node.injEq]; );                                     /- := ( colours = [] ) ↔ ( out = IND.START ) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge RULE.CENTER out colour dep_out ∈ RULE.OUTGOING -/
                                   intro out out_cases;                                                                       /- := ( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out ) -/
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial; );
  | tail _ ind_cases => trivial;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Pre-Collapse: Type0 Hypothesis (Top Formula) -/
  theorem PreCol_Of_PreCollapse_Top {RULE : Neighborhood} :
    ( type0_hypothesis RULE ) →
    ---------------------------
    ( type1_pre_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type0_hypothesis] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.outgoing];
  simp only [pre_collapse.direct];
  simp only [pre_collapse.indirect];
  simp only [type1_pre_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                   /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                   /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                   /- := RULE.CENTER.COLLAPSED = false -/
  apply And.intro ( by exact prop_pst; );                   /- := RULE.CENTER.PAST = [] -/
  /- Check Deduction Edges -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );          /- := ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) -/
  apply And.intro ( by simp only [List.length]; trivial; );     /- := List.length (RULE.INCOMING) ≤ 2 -/
  apply And.intro ( by simp only [List.cons.injEq];             /- := RULE.OUTGOING = [out] -/
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;               /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check Ancestral Paths -/
  apply And.intro ( by trivial; );                                      /- := RULE.DIRECT = [] -/
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;               /- := ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) -/
                       apply DEFINE.Def_Check_Path_Starts ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_starts]; );
  apply And.intro ( by simp only [List.length]; );                      /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
  apply And.intro ( by intro ind ind_mem;                               /- := ind.COLOURS = [0, RULE.CENTER.NUMBER] -/
                       apply DEFINE.Def_Check_Path_Colours ind_mem;
                       simp only [DEFINE.check_path_colours]; );
  /- Check Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro inc inc_cases; trivial; );
  /- Check Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₁];
                       apply Or.inl; simp only [type_outgoing₁.check_h₁, and_assoc];                   /- := Type 0 Hypothesis -/
                       cases out_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and];
                                   apply And.intro ( by exact prop_hpt; );                             /- := CENTER.HYPOTHESIS = true -/
                                   apply And.intro ( by exact prop_out_nbr; );                         /- := OUT.END.NUMBER > 0 -/
                                   trivial;                                                            /- := OUT.COLOUR = 0 -/
                       | tail _ out_cases => trivial; );
  /- Check Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  intro ind ind_cases; trivial;
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T1_Of_T0


namespace COVERAGE.T3_Of_T2
  --333 set_option trace.Meta.Tactic.simp true
  /- Pre-Collapse: Type2 ⊇-Elimination -/
  theorem PreCol_Of_PreCollapse_Elim {RULE : Neighborhood} :
    ( type2_elimination RULE ) →
    ---------------------------
    ( type3_pre_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type2_elimination] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro anc_nbr prop_type =>
  cases prop_type with | intro anc_lvl prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro anc_fml prop_type =>
  cases prop_type with | intro major_hpt prop_type =>
  cases prop_type with | intro minor_hpt prop_type =>
  cases prop_type with | intro out_hpt prop_type =>
  cases prop_type with | intro major_dep prop_type =>
  cases prop_type with | intro minor_dep prop_type =>
  cases prop_type with | intro past prop_type =>
  cases prop_type with | intro colour prop_type =>
  cases prop_type with | intro pasts prop_type =>
  cases prop_type with | intro colours prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_anc_nbr prop_type =>
  cases prop_type with | intro prop_anc_lvl prop_type =>
  cases prop_type with | intro prop_colour prop_type =>
  cases prop_type with | intro prop_pasts prop_type =>
  cases prop_type with | intro prop_colours prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.outgoing];
  simp only [pre_collapse.direct];
  simp only [pre_collapse.indirect];
  simp only [pre_collapse.indirect.move_up];
  simp only [type3_pre_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                   /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                   /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                   /- := RULE.CENTER.COLLAPSED = false -/
  apply And.intro ( by exact prop_pst; );                   /- := RULE.CENTER.PAST = [] -/
  /- Check Deduction Edges -/
  apply And.intro ( by simp only [reduceCtorEq];            /- := ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) -/
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );     /- := List.length (RULE.INCOMING) ≤ 2 -/
  apply And.intro ( by simp only [List.cons.injEq];             /- := RULE.OUTGOING = [out] -/
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;               /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check Ancestral Paths -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );                  /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );                  /- := ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
  apply And.intro ( by exact Or.inl trivial; );                         /- := ( RULE.DIRECT = [] ) ∨ ( RULE.DIRECT = [dir] ) -/
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;               /- := ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) -/
                       apply DEFINE.Def_Check_Path_Starts ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_starts];
                       simp only [DEFINE.check_path_starts.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );                      /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
  /- Check Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and, and_true];
                                   apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );                                  /- := INC.START.NUMBER > 0 -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro RULE.CENTER.NUMBER;                                                   /- colour (Path Notation) -/
                                   apply Exists.intro (colour::colours);                                                    /- colours (Path Notation) -/
                                   apply Exists.intro (node anc_nbr anc_lvl anc_fml false false []);                        /- anc (Ancestral Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                       | tail _ inc_cases => cases inc_cases with
                                             | head _ => simp only [Vertex.node.injEq, true_and, and_true];
                                                         apply And.intro ( by exact prop_inc_nbr; );                                              /- := INC.START.NUMBER > 0 -/
                                                         /- Match-Verification Loop: -/
                                                         apply Exists.intro RULE.CENTER.NUMBER;                                                   /- colour (Path Notation) -/
                                                         apply Exists.intro (colour::colours);                                                    /- colours (Path Notation) -/
                                                         apply Exists.intro (node anc_nbr anc_lvl anc_fml false false []);                        /- anc (Ancestral Node) -/
                                                         exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                             | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₃];
                       apply Or.inr; apply Or.inr; simp only [type_outgoing₃.check_ie₃, and_assoc];                 /- := Type 2 Elimination -/
                       cases out_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );                                   /- := CENTER.HYPOTHESIS = false ∨ CENTER.COLLAPSED = true -/
                                   apply And.intro ( by exact prop_out_nbr; );                                      /- := OUT.END.NUMBER > 0 -/
                                   apply And.intro ( by apply Exists.intro past;                                    /- := check_numbers (past::pasts) ∧ OUT.END.PAST = (past::pasts) -/
                                                        apply Exists.intro pasts;
                                                        simp only [prop_pasts];
                                                        trivial; );
                                   apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                    /- := OUT.COLOUR ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (colour::colours);                                                    /- colours (Path Notation) -/
                                   apply Exists.intro (node inc_nbr (RULE.CENTER.LEVEL+1) antecedent minor_hpt false []);   /- inc (Incoming Node) -/
                                   apply Exists.intro (node anc_nbr anc_lvl anc_fml false false []);                        /- anc (Ancestral Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                       | tail _ out_cases => trivial; );
  /- Check Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro dir dir_cases; trivial; );
  /- Check Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Vertex.node.injEq, true_and];
              apply And.intro ( by exact prop_anc_nbr; );                                         /- := IND.START.NUMBER > 0 -/
              apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := IND.START.LEVEL ≤ RULE.CENTER.LEVEL - 1 -/
                                   simp only [List.length];
                                   exact Nat.le_add_right anc_lvl (List.length colours + 1); );
              apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );                             /- := IND.END.NUMBER > 0 -/
              apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := IND.START.LEVEL + List.length (IND.COLOURS) = RULE.CENTER.LEVEL + 1 -/
                                   simp only [List.length];
                                   trivial; );
              apply Exists.intro RULE.CENTER.NUMBER;                                              /- colour (Path Notation) -/
              apply Exists.intro (colour::colours);                                               /- colours (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colours; );    /- := check_numbers (colour::colours) -/
              apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                       /- := colour ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
              apply And.intro ( by trivial; );                                                    /- := IND.COLOURS = (0::colour::colours) -/
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro #major_dep;                                                              /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge IND.END RULE.CENTER 0 dep_inc ∈ RULE.INCOMING -/
                                   intro inc inc_cases;                                                                       /- := ( INC.START = IND.END ) ↔ ( INC = edge IND.END RULE.CENTER 0 dep_inc ) -/
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Resolve Missmatch: -/
                                   simp only [Deduction.edge.injEq, true_and, and_true];
                                   simp only [Vertex.node.injEq, true_and, and_true];
                                   simp only [iff_self_and, and_imp];
                                   have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                   simp only [ne_eq, eq_comm] at succ_ne_self;
                                   intro succ_eq_self;
                                   trivial; )
                              ( by apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL-1) out_fml out_hpt true (past::pasts));  /- out (Outgoing Node) -/
                                   apply Exists.intro (minor_dep ∪ major_dep);                                                  /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by simp only [Vertex.node.injEq];                                          /- := ( colours = [] ) ↔ ( out = IND.START ) -/
                                                        simp only [reduceCtorEq];
                                                        simp only [false_iff, not_and];
                                                        intro _ prop_ctr_lvl;
                                                        rewrite [←prop_anc_lvl] at prop_ctr_lvl;
                                                        simp only [List.length] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_assoc (Nat.le_add_left 1 (List.length colours+1))] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_cancel] at prop_ctr_lvl;
                                                        have lt_self := Nat.add_lt_add_left (Nat.zero_lt_succ (List.length colours)) anc_lvl;
                                                        simp only [prop_ctr_lvl, Nat.add_zero, Nat.lt_irrefl] at lt_self; );
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );      /- := edge RULE.CENTER out colour dep_out ∈ RULE.OUTGOING -/
                                   intro out out_cases;                                                                         /- := ( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out ) -/
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial; );
  | tail _ ind_cases => cases ind_cases with
                        | head _ => simp only [Vertex.node.injEq, true_and];
                                    apply And.intro ( by exact prop_anc_nbr; );                                         /- := IND.START.NUMBER > 0 -/
                                    apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := IND.START.LEVEL ≤ RULE.CENTER.LEVEL - 1 -/
                                                         simp only [List.length];
                                                         exact Nat.le_add_right anc_lvl (List.length colours + 1); );
                                    apply And.intro ( by exact prop_inc_nbr; );                                         /- := IND.END.NUMBER > 0 -/
                                    apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := IND.START.LEVEL + List.length (IND.COLOURS) = RULE.CENTER.LEVEL + 1 -/
                                                         simp only [List.length];
                                                         trivial; );
                                    apply Exists.intro RULE.CENTER.NUMBER;                                              /- colour (Path Notation) -/
                                    apply Exists.intro (colour::colours);                                               /- colours (Path Notation) -/
                                    apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colours; );    /- := check_numbers (colour::colours) -/
                                    apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                       /- := colour ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                    apply And.intro ( by trivial; );                                                    /- := IND.COLOURS = (0::colour::colours) -/
                                    /- Match-Verification Loop: -/
                                    exact And.intro ( by apply Exists.intro #minor_dep;                                                              /- dep_inc (Incoming Dependency) -/
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge IND.END RULE.CENTER 0 dep_inc ∈ RULE.INCOMING -/
                                                         intro inc inc_cases;                                                                       /- := ( INC.START = IND.END ) ↔ ( INC = edge IND.END RULE.CENTER 0 dep_inc ) -/
                                                         apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                                         simp only [DEFINE.check_path_incoming];
                                                         /- Resolve Missmatch: -/
                                                         simp only [Deduction.edge.injEq, true_and, and_true];
                                                         simp only [Vertex.node.injEq, true_and, and_true];
                                                         simp only [iff_self_and, and_imp];
                                                         have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                                         simp only [ne_eq] at succ_ne_self;
                                                         intro succ_eq_self;
                                                         trivial; )
                                                    ( by apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL-1) out_fml out_hpt true (past::pasts));  /- out (Outgoing Node) -/
                                                         apply Exists.intro (minor_dep ∪ major_dep);                                                  /- dep_out (Outgoing Dependency) -/
                                                         apply And.intro ( by simp only [Vertex.node.injEq];                                          /- := ( colours = [] ) ↔ ( out = IND.START ) -/
                                                                              simp only [reduceCtorEq];
                                                                              simp only [false_iff, not_and];
                                                                              intro _ prop_ctr_lvl;
                                                                              rewrite [←prop_anc_lvl] at prop_ctr_lvl;
                                                                              simp only [List.length] at prop_ctr_lvl;
                                                                              simp only [Nat.add_sub_assoc (Nat.le_add_left 1 (List.length colours+1))] at prop_ctr_lvl;
                                                                              simp only [Nat.add_sub_cancel] at prop_ctr_lvl;
                                                                              have lt_self := Nat.add_lt_add_left (Nat.zero_lt_succ (List.length colours)) anc_lvl;
                                                                              simp only [prop_ctr_lvl, Nat.add_zero, Nat.lt_irrefl] at lt_self; );
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );      /- := edge RULE.CENTER out colour dep_out ∈ RULE.OUTGOING -/
                                                         intro out out_cases;                                                                         /- := ( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out ) -/
                                                         apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                                         /- Perfect Match! -/
                                                         simp only [DEFINE.check_path_outgoing];
                                                         trivial; );
                        | tail _ ind_cases => trivial;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Pre-Collapse: Type2 ⊇-Introduction -/
  theorem PreCol_Of_PreCollapse_Intro {RULE : Neighborhood} :
    ( type2_introduction RULE ) →
    ---------------------------
    ( type3_pre_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type2_introduction] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro anc_nbr prop_type =>
  cases prop_type with | intro anc_lvl prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro consequent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro anc_fml prop_type =>
  cases prop_type with | intro out_hpt prop_type =>
  cases prop_type with | intro inc_dep prop_type =>
  cases prop_type with | intro past prop_type =>
  cases prop_type with | intro colour prop_type =>
  cases prop_type with | intro pasts prop_type =>
  cases prop_type with | intro colours prop_type =>
  cases prop_type with | intro prop_fml prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_anc_nbr prop_type =>
  cases prop_type with | intro prop_anc_lvl prop_type =>
  cases prop_type with | intro prop_colour prop_type =>
  cases prop_type with | intro prop_pasts prop_type =>
  cases prop_type with | intro prop_colours prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.outgoing];
  simp only [pre_collapse.direct];
  simp only [pre_collapse.indirect];
  simp only [pre_collapse.indirect.move_up];
  simp only [type3_pre_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                   /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                   /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                   /- := RULE.CENTER.COLLAPSED = false -/
  apply And.intro ( by exact prop_pst; );                   /- := RULE.CENTER.PAST = [] -/
  /- Check Deduction Edges -/
  apply And.intro ( by simp only [reduceCtorEq];            /- := ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) -/
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );     /- := List.length (RULE.INCOMING) ≤ 2 -/
  apply And.intro ( by simp only [List.cons.injEq];             /- := RULE.OUTGOING = [out] -/
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;               /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check Ancestral Paths -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );                  /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );                  /- := ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
  apply And.intro ( by exact Or.inl trivial; );                         /- := ( RULE.DIRECT ≠ [] ) ∨ ( RULE.DIRECT = [dir] ) -/
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;               /- := ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) -/
                       apply DEFINE.Def_Check_Path_Starts ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_starts];
                       simp only [DEFINE.check_path_starts.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );                      /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
  /- Check Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and, and_true];
                                   apply And.intro ( by exact prop_inc_nbr; );                                              /- := INC.START.NUMBER > 0 -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro RULE.CENTER.NUMBER;                                                   /- colour (Path Notation) -/
                                   apply Exists.intro (colour::colours);                                                    /- colours (Path Notation) -/
                                   apply Exists.intro (node anc_nbr anc_lvl anc_fml false false []);                        /- anc (Ancestral Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                       | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₃];
                       apply Or.inr; apply Or.inr; simp only [type_outgoing₃.check_ie₃, and_assoc];                 /- := Type 2 Introduction -/
                       cases out_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );                                   /- := CENTER.HYPOTHESIS = false ∨ CENTER.COLLAPSED = true -/
                                   apply And.intro ( by exact prop_out_nbr; );                                      /- := OUT.END.NUMBER > 0 -/
                                   apply And.intro ( by apply Exists.intro past;                                    /- := check_numbers (past::pasts) ∧ OUT.END.PAST = (past::pasts) -/
                                                        apply Exists.intro pasts;
                                                        simp only [prop_pasts];
                                                        trivial; );
                                   apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                    /- := OUT.COLOUR ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (colour::colours);                                                    /- colours (Path Notation) -/
                                   apply Exists.intro (node inc_nbr (RULE.CENTER.LEVEL+1) consequent false false []);       /- inc (Incoming Node) -/
                                   apply Exists.intro (node anc_nbr anc_lvl anc_fml false false []);                        /- anc (Ancestral Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                       | tail _ out_cases => trivial; );
  /- Check Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro dir dir_cases; trivial; );
  /- Check Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Vertex.node.injEq, true_and];
              apply And.intro ( by exact prop_anc_nbr; );                                         /- := IND.START.NUMBER > 0 -/
              apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := IND.START.LEVEL ≤ RULE.CENTER.LEVEL - 1 -/
                                   simp only [List.length];
                                   exact Nat.le_add_right anc_lvl (List.length colours + 1); );
              apply And.intro ( by exact prop_inc_nbr; );                                         /- := IND.END.NUMBER > 0 -/
              apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := IND.START.LEVEL + List.length (IND.COLOURS) = RULE.CENTER.LEVEL + 1 -/
                                   simp only [List.length];
                                   trivial; );
              apply Exists.intro RULE.CENTER.NUMBER;                                              /- colour (Path Notation) -/
              apply Exists.intro (colour::colours);                                               /- colours (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colours; );    /- := check_numbers (colour::colours) -/
              apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                       /- := colour ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
              apply And.intro ( by trivial; );                                                    /- := IND.COLOURS = (0::colour::colours) -/
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro #inc_dep;                                                               /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );    /- := edge IND.END RULE.CENTER 0 dep_inc ∈ RULE.INCOMING -/
                                   intro inc inc_cases;                                                                       /- := ( INC.START = IND.END ) ↔ ( INC = edge IND.END RULE.CENTER 0 dep_inc ) -/
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Perfect Match! -/
                                   trivial; )
                              ( by apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL-1) out_fml out_hpt true (past::pasts));  /- out (Outgoing Node) -/
                                   apply Exists.intro (inc_dep − [antecedent]);                                                 /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by simp only [Vertex.node.injEq];                                          /- := ( colours = [] ) ↔ ( out = IND.START ) -/
                                                        simp only [reduceCtorEq];
                                                        simp only [false_iff, not_and];
                                                        intro _ prop_ctr_lvl;
                                                        rewrite [←prop_anc_lvl] at prop_ctr_lvl;
                                                        simp only [List.length] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_assoc (Nat.le_add_left 1 (List.length colours+1))] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_cancel] at prop_ctr_lvl;
                                                        have lt_self := Nat.add_lt_add_left (Nat.zero_lt_succ (List.length colours)) anc_lvl;
                                                        simp only [prop_ctr_lvl, Nat.add_zero, Nat.lt_irrefl] at lt_self; );
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );      /- := edge RULE.CENTER out colour dep_out ∈ RULE.OUTGOING -/
                                   intro out out_cases;                                                                         /- := ( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out ) -/
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial; );
  | tail _ ind_cases => trivial;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Pre-Collapse: Type2 Hypothesis (Top Formula) -/
  theorem PreCol_Of_PreCollapse_Top {RULE : Neighborhood} :
    ( type2_hypothesis RULE ) →
    ---------------------------
    ( type3_pre_collapse (pre_collapse RULE) ) := by
  intro prop_type;
  simp only [type2_hypothesis] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro anc_nbr prop_type =>
  cases prop_type with | intro anc_lvl prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro anc_fml prop_type =>
  cases prop_type with | intro out_hpt prop_type =>
  cases prop_type with | intro past prop_type =>
  cases prop_type with | intro colour prop_type =>
  cases prop_type with | intro pasts prop_type =>
  cases prop_type with | intro colours prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_anc_nbr prop_type =>
  cases prop_type with | intro prop_anc_lvl prop_type =>
  cases prop_type with | intro prop_colour prop_type =>
  cases prop_type with | intro prop_pasts prop_type =>
  cases prop_type with | intro prop_colours prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.outgoing];
  simp only [pre_collapse.direct];
  simp only [pre_collapse.direct.paint];
  simp only [pre_collapse.indirect];
  simp only [type3_pre_collapse];
  /- Check Center -/
  apply And.intro ( by exact prop_nbr; );                   /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvl; );                   /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by exact prop_col; );                   /- := RULE.CENTER.COLLAPSED = false -/
  apply And.intro ( by exact prop_pst; );                   /- := RULE.CENTER.PAST = [] -/
  /- Check Deduction Edges -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );          /- := ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) -/
  apply And.intro ( by simp only [List.length]; trivial; );     /- := List.length (RULE.INCOMING) ≤ 2 -/
  apply And.intro ( by simp only [List.cons.injEq];             /- := RULE.OUTGOING = [out] -/
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;               /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check Ancestral Paths -/
  apply And.intro ( by simp only [List.cons_ne_nil];            /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
                       simp only [imp_false];
                       simp only [Bool.not_eq_false];
                       exact prop_hpt; );
  apply And.intro ( by intros; exact prop_hpt; );               /- := ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
  apply And.intro ( by simp only [List.cons.injEq];             /- := ( RULE.DIRECT ≠ [] ) ∨ ( RULE.DIRECT = [dir] ) -/
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       simp only [and_true, or_true]; );
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;               /- := ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) -/
                       apply DEFINE.Def_Check_Path_Starts ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_starts]; );
  apply And.intro ( by simp only [List.length]; );                      /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
  /- Check Incoming Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro inc inc_cases; trivial; );
  /- Check Outgoing Edges -/--------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₃];
                       apply Or.inr; apply Or.inl; simp only [type_outgoing₃.check_h₃, and_assoc];                  /- := Type 2 hypothesis -/
                       cases out_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and];
                                   apply And.intro ( by exact prop_hpt; );                                          /- := CENTER.HYPOTHESIS = true -/
                                   apply And.intro ( by exact prop_out_nbr; );                                      /- := OUT.END.NUMBER > 0 -/
                                   apply And.intro ( by apply Exists.intro past;                                    /- := check_numbers (past::pasts) ∧ OUT.END.PAST = (past::pasts) -/
                                                        apply Exists.intro pasts;
                                                        simp only [prop_pasts];
                                                        trivial; );
                                   apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                    /- := OUT.COLOUR ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (colour::colours);                                                    /- colours (Path Notation) -/
                                   apply Exists.intro (node anc_nbr anc_lvl anc_fml false false []);                        /- anc (Ancestral Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );            /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                       | tail _ out_cases => trivial; );
  /- Check Direct Paths -/----------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by intro dir dir_cases;
                       simp only [type_direct, type_direct.check, and_assoc];
                       cases dir_cases with
                       | head _ => simp only [Vertex.node.injEq, true_and];
                                   apply And.intro ( by exact prop_anc_nbr; );                                         /- := DIR.START.NUMBER > 0 -/
                                   apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := DIR.START.LEVEL ≤ RULE.CENTER.LEVEL - 1 -/
                                                        simp only [List.length];
                                                        exact Nat.le_add_right anc_lvl (List.length colours + 1); );
                                   apply And.intro ( by rewrite [←prop_anc_lvl];                                       /- := DIR.START.LEVEL + List.length (DIR.COLOURS) = RULE.CENTER.LEVEL + 1 -/
                                                        simp only [List.length]; );
                                   apply Exists.intro RULE.CENTER.NUMBER;                                              /- colour₁ (Path Notation) -/
                                   apply Exists.intro colour;                                                          /- colour₂ (Path Notation) -/
                                   apply Exists.intro colours;                                                         /- colours (Path Notation) -/
                                   apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colours; );    /- := check_numbers (colour::colours) -/
                                   apply And.intro ( by exact List.Mem.head RULE.CENTER.PAST; );                       /- := colour ∈ (RULE.CENTER.NUMBER::RULE.CENTER.PAST) -/
                                   apply And.intro ( by trivial; );                                                    /- := DIR.COLOURS = (0::colour::colours) -/
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (node out_nbr (RULE.CENTER.LEVEL-1) out_fml out_hpt true (past::pasts));  /- out (Outgoing Node) -/
                                   apply Exists.intro ([RULE.CENTER.FORMULA]);                                                  /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by trivial; );                                                             /- := out.COLLAPSED = true -/
                                   apply And.intro ( by exact prop_colour; );                                                   /- := colour₂ ∈ (out.NUMBER::out.PAST) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );      /- := edge RULE.CENTER out colour dep_out ∈ RULE.OUTGOING -/
                                   intro out out_cases;                                                                         /- := ( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out ) -/
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial;
                       | tail _ ind_cases => trivial; );
  /- Check Indirect Paths -/--------------------------------------------------------------------------------------------------------------------------
  intro ind ind_cases; trivial;
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T3_Of_T2


namespace COVERAGE.T1_Of_T1.NODES
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Collapse Execution (Type 0 & Type 0 => Type 1) (Nodes) -/
  theorem Col_Of_Collapse_Pre_Pre {RULEᵤ RULEᵥ : Neighborhood} :
    ( check_collapse_nodes RULEᵤ RULEᵥ ) →
    ( type1_pre_collapse RULEᵤ ) →
    ( type1_pre_collapse RULEᵥ ) →
    ---------------------------
    ( type1_collapse (collapse RULEᵤ RULEᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  --
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  --
  simp only [type1_pre_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_startsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_indirectᵤ =>
  --
  cases prop_out_unitᵤ with | intro outᵤ prop_out_unitᵤ =>
  --
  simp only [type1_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_startsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_indirectᵥ =>
  --
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  --
  simp only [collapse];
  simp only [collapse.center];
  simp only [type1_collapse];
  /- Check Center-/
  apply And.intro ( by exact prop_nbrᵤ; );                                        /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvlᵤ; );                                        /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by trivial; );                                                /- := RULE.CENTER.COLLAPSED = true -/
  apply And.intro ( by apply Exists.intro RULEᵥ.CENTER.NUMBER;                    /- := check_numbers (past :: pasts) ∧ RULE.CENTER.PAST = (past::pasts) -/
                       apply Exists.intro RULEᵤ.CENTER.PAST;
                       apply And.intro ( by simp only [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ; );
                       trivial; );
  /- Check Deduction Edges -/
  apply And.intro ( by intro prop_inc_nil;                                        /- := ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];                                                                    /- := RULE.OUTGOING = (out::outs) -/
                       apply Exists.intro ( edge ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )                        /- RULEᵥ.OUTGOING -/
                                                 ( outᵥ.END )
                                                 ( outᵥ.COLOUR )
                                                 ( outᵥ.DEPENDENCY ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )   /- RULEᵤ.OUTGOING -/
                                                                      ( RULEᵤ.OUTGOING ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;                          /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [Deduction.edge.injEq'];
                       --
                       simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colourᵥ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colourᵥ;
                       --
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;                              /- := out₁ = outᵥ -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];                /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             --
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;                 /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Colour₂ᵤ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.COLOUR = 0 ∨ out₂.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₂ᵤ ⊢;
                                                             have NE_Colour : outᵥ.COLOUR ≠ out₂.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Colour, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];                /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;                              /- := out₂ = outᵥ -/
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;                 /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Colour₁ᵤ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.COLOUR = 0 ∨ out₁.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₁ᵤ ⊢;
                                                             have NE_Colour : out₁.COLOUR ≠ outᵥ.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Colour, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];              /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];              /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;               /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.START = RULEᵤ.CENTER -/
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;               /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [Deduction.edge.injEq] at Out_Start₁ᵤ Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ; );
  /- Check Ancestral Paths -/
  apply And.intro ( by rewrite [prop_dir_nilᵤ, prop_dir_nilᵥ];        /- := RULE.DIRECT = [] -/
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by simp only [List.length_append];                /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by intro ind ind_cases;                           /- := ind.COLOURS = [0, colour] -/
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at ind_cases;
                       cases ind_cases with
                       | inl ind_casesᵥ => apply Exists.intro RULEᵥ.CENTER.NUMBER;
                                           exact prop_ind_coloursᵥ ind_casesᵥ;
                       | inr ind_casesᵤ => apply Exists.intro RULEᵤ.CENTER.NUMBER;
                                           exact prop_ind_coloursᵤ ind_casesᵤ; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;            /- := inc ∈ RULEᵥ.INCOMING -/
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;                        /- := type_incoming.check inc RULEᵥ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Startᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Endᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colourᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                            /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵥ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵥ with | intro Colourᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Coloursᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply Exists.intro Colourᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;            /- := inc ∈ RULEᵤ.INCOMING -/
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;                        /- := type_incoming.check inc RULEᵤ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Startᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Endᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colourᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                             /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵤ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵤ with | intro Colourᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Coloursᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply Exists.intro Colourᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;          /- := out ∈ RULEᵥ.OUTGOING -/
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;                      /- := type_outgoing.check out RULEᵥ.CENTER -/
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Startₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Endₕ₁ᵥ Prop_Colourₕ₁ᵥ =>
                                                                     --
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                          exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );    /- := Start Node -/
                                                                     apply And.intro ( by rewrite [prop_eq_lvl];                               /- := End Node -/
                                                                                          exact Prop_Endₕ₁ᵥ; );
                                                                     exact Prop_Colourₕ₁ᵥ;                                                     /- := Colours -/
                                           | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Startᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Endᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colourᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      --
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                      apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                      apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                           exact Prop_Endᵢₑ₁ᵥ; );
                                                                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₁ᵥ;            /- := Colours -/
                                                                                           rewrite [Prop_Colourᵢₑ₁ᵥ];
                                                                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                      /- := Check Outgoing-Indirect Duo: -/
                                                                      cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      --
                                                                      apply Exists.intro Incᵢₑ₁ᵥ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                  apply Or.inl;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;          /- := out ∈ RULEᵤ.OUTGOING -/
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;                      /- := type_outgoing.check out RULEᵤ.CENTER -/
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Startₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Endₕ₁ᵤ Prop_Colourₕ₁ᵤ =>
                                                                     --
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                          exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                     apply And.intro ( by exact Prop_Endₕ₁ᵤ; );                                /- := End Node -/
                                                                     exact Prop_Colourₕ₁ᵤ;                                                     /- := Colours -/
                                           | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Startᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Endᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colourᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      --
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                      apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );                        /- := Start Node -/
                                                                      apply And.intro ( by exact Prop_Endᵢₑ₁ᵤ; );                                                   /- := End Node -/
                                                                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₁ᵤ;                /- := Colours -/
                                                                                           cases Prop_Colourᵢₑ₁ᵤ with
                                                                                           | inl Prop_NBR_Colourᵢₑ₁ᵤ => rewrite [Prop_NBR_Colourᵢₑ₁ᵤ];
                                                                                                                        exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                           | inr Prop_PST_Colourᵢₑ₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                            ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₁ᵤ ); );
                                                                      /- := Check Outgoing-Indirect Duo: -/
                                                                      cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      --
                                                                      apply Exists.intro Incᵢₑ₁ᵤ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                  apply Or.inr;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Startᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Endᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      --
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Start Node -/
                                           exact Prop_Startᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := End Node -/
                                           exact Prop_Endᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Colours -/
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colourᵥ;
                      apply Exists.intro Coloursᵥ;
                      apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;
                                           rewrite [Prop_Colourᵥ];
                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                      apply And.intro ( by exact Prop_Coloursᵥ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;      /- := all_inc.END = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵥᵥ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;              /- := all_inc.START ≠ IND.END -/
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );
                      /- := Check Indirect-Outgoing Duo: -/
                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      --
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by exact Prop_Out_Colᵥ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colourᵥᵤ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;                                /- := Colour = RULEᵥ.CENTER.NUMBER -/
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵥ : all_outᵥ.COLOUR ≠ Colourᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 rewrite [EQ_Colour, Prop_Colourᵥ] at Ind_Out_Colourᵥᵤ;
                                                                                                 cases Ind_Out_Colourᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Startᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Endᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      --
                      apply And.intro ( by exact Prop_Startᵤ; );           /- := Start Node -/
                      apply And.intro ( by exact Prop_Endᵤ; );             /- := End Node -/
                      apply And.intro ( by exact Prop_Levelᵤ; );           /- := Colours -/
                      apply Exists.intro Colourᵤ;
                      apply Exists.intro Coloursᵤ;
                      apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵤ;
                                           cases Prop_Colourᵤ with
                                           | inl Prop_NBR_Colourᵤ => rewrite [Prop_NBR_Colourᵤ];
                                                                     exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                           | inr Prop_PST_Colourᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                         ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵤ ); );
                      apply And.intro ( by exact Prop_Coloursᵤ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;              /- := IND.END ≠ all_inc.START -/
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;      /- := all_inc.END = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵤᵤ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      --
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by exact Prop_Out_Colᵤ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour dep_out ∈ OUTGOING -/
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colourᵤᵥ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colourᵤᵥ;
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵤ : all_outᵤ.COLOUR ≠ Colourᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 apply absurd Prop_Colourᵤ;                /- := Colour ∉ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                                                 cases Ind_Out_Colourᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Colour, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Iff_Mem_Unit];
                                                                                                                  exact Nat.ne_of_lt prop_nbrᵤ;
                                                                                                 | inr GT_Zero => rewrite [←EQ_Colour, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

  /- Lemma: Collapse Execution (Type 1 & Type 0 => Type 1) (Nodes) -/
  theorem Col_Of_Collapse_Col_Pre {RULEᵤ RULEᵥ : Neighborhood} :
    ( check_collapse_nodes RULEᵤ RULEᵥ ) →
    ( type1_collapse RULEᵤ ) →
    ( type1_pre_collapse RULEᵥ ) →
    ---------------------------
    ( type1_collapse (collapse RULEᵤ RULEᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  --
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  --
  simp only [type1_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_indirectᵤ =>
  --
  cases prop_pstᵤ with | intro pastᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro pastsᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro prop_check_pastᵤ prop_pstᵤ =>
  --
  cases prop_out_consᵤ with | intro outᵤ prop_out_consᵤ =>
  cases prop_out_consᵤ with | intro outsᵤ prop_out_consᵤ =>
  --
  simp only [type1_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_startsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_indirectᵥ =>
  --
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  --
  simp only [collapse];
  simp only [collapse.center];
  simp only [type1_collapse];
  /- Check Center-/
  apply And.intro ( by exact prop_nbrᵤ; );                                        /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvlᵤ; );                                        /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by trivial; );                                                /- := RULE.CENTER.COLLAPSED = true -/
  apply And.intro ( by apply Exists.intro RULEᵥ.CENTER.NUMBER;                    /- := check_numbers (past :: pasts) ∧ RULE.CENTER.PAST = (past::pasts) -/
                       apply Exists.intro RULEᵤ.CENTER.PAST;
                       apply And.intro ( by rewrite [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ prop_check_pastᵤ; );
                       trivial; );
  /- Check Deduction Edges -/
  apply And.intro ( by intro prop_inc_nil;                                        /- := ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];                                                                    /- := RULE.OUTGOING = (out::outs) -/
                       apply Exists.intro ( edge ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )                        /- RULEᵥ.OUTGOING -/
                                                 ( outᵥ.END )
                                                 ( outᵥ.COLOUR )
                                                 ( outᵥ.DEPENDENCY ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )   /- RULEᵤ.OUTGOING -/
                                                                      ( RULEᵤ.OUTGOING ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;                          /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [Deduction.edge.injEq'];
                       --
                       simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colourᵥ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colourᵥ;
                       --
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;                              /- := out₁ = outᵥ -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];                /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             --
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;                 /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Colour₂ᵤ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.COLOUR = 0 ∨ out₂.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₂ᵤ ⊢;
                                                             have NE_Colour : outᵥ.COLOUR ≠ out₂.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Colour, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];                /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;                              /- := out₂ = outᵥ -/
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;                 /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Colour₁ᵤ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.COLOUR = 0 ∨ out₁.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₁ᵤ ⊢;
                                                             have NE_Colour : out₁.COLOUR ≠ outᵥ.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Colour, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];              /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];              /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;               /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.START = RULEᵤ.CENTER -/
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;               /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [Deduction.edge.injEq] at Out_Start₁ᵤ Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ; );
  apply And.intro ( by rewrite [prop_dir_nilᵤ, prop_dir_nilᵥ];        /- := RULE.DIRECT = [] -/
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by simp only [List.length_append];                /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by intro ind ind_cases;                           /- := ind.COLOURS = [0, colour] -/
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at ind_cases;
                       cases ind_cases with
                       | inl ind_casesᵥ => apply Exists.intro RULEᵥ.CENTER.NUMBER;
                                           exact prop_ind_coloursᵥ ind_casesᵥ;
                       | inr ind_casesᵤ => exact prop_ind_coloursᵤ ind_casesᵤ; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;            /- := inc ∈ RULEᵥ.INCOMING -/
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;                        /- := type_incoming.check inc RULEᵥ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Startᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Endᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colourᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                            /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵥ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵥ with | intro Colourᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Coloursᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply Exists.intro Colourᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;            /- := inc ∈ RULEᵤ.INCOMING -/
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;                        /- := type_incoming.check inc RULEᵤ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Startᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Endᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colourᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                             /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵤ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵤ with | intro Colourᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Coloursᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply Exists.intro Colourᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;          /- := out ∈ RULEᵥ.OUTGOING -/
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;                      /- := type_outgoing.check out RULEᵥ.CENTER -/
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Startₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Endₕ₁ᵥ Prop_Colourₕ₁ᵥ =>
                                                                     --
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                          exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );    /- := Start Node -/
                                                                     apply And.intro ( by rewrite [prop_eq_lvl];                               /- := End Node -/
                                                                                          exact Prop_Endₕ₁ᵥ; );
                                                                     exact Prop_Colourₕ₁ᵥ;                                                     /- := Colours -/
                                           | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Startᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Endᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colourᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      --
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                      apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                      apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                           exact Prop_Endᵢₑ₁ᵥ; );
                                                                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₁ᵥ;            /- := Colours -/
                                                                                           rewrite [Prop_Colourᵢₑ₁ᵥ];
                                                                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                      /- := Check Outgoing-Indirect Duo: -/
                                                                      cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      --
                                                                      apply Exists.intro Incᵢₑ₁ᵥ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                  apply Or.inl;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;          /- := out ∈ RULEᵤ.OUTGOING -/
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;                      /- := type_outgoing.check out RULEᵤ.CENTER -/
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Startₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Endₕ₁ᵤ Prop_Colourₕ₁ᵤ =>
                                                                     --
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                          exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                     apply And.intro ( by exact Prop_Endₕ₁ᵤ; );                                /- := End Node -/
                                                                     exact Prop_Colourₕ₁ᵤ;                                                     /- := Colours -/
                                           | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Startᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Endᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colourᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      --
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                      apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );                        /- := Start Node -/
                                                                      apply And.intro ( by exact Prop_Endᵢₑ₁ᵤ; );                                                   /- := End Node -/
                                                                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₁ᵤ;                /- := Colours -/
                                                                                           cases Prop_Colourᵢₑ₁ᵤ with
                                                                                           | inl Prop_NBR_Colourᵢₑ₁ᵤ => rewrite [Prop_NBR_Colourᵢₑ₁ᵤ];
                                                                                                                        exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                           | inr Prop_PST_Colourᵢₑ₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                            ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₁ᵤ ); );
                                                                      /- := Check Outgoing-Indirect Duo: -/
                                                                      cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      --
                                                                      apply Exists.intro Incᵢₑ₁ᵤ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                  apply Or.inr;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Startᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Endᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      --
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Start Node -/
                                           exact Prop_Startᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := End Node -/
                                           exact Prop_Endᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Colours -/
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colourᵥ;
                      apply Exists.intro Coloursᵥ;
                      apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;
                                           rewrite [Prop_Colourᵥ];
                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                      apply And.intro ( by exact Prop_Coloursᵥ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;      /- := all_inc.END = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵥᵥ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;              /- := all_inc.START ≠ IND.END -/
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );
                      /- := Check Indirect-Outgoing Duo: -/
                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      --
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by exact Prop_Out_Colᵥ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colourᵥᵤ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;                                /- := Colour = RULEᵥ.CENTER.NUMBER -/
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵥ : all_outᵥ.COLOUR ≠ Colourᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 rewrite [EQ_Colour, Prop_Colourᵥ] at Ind_Out_Colourᵥᵤ;
                                                                                                 cases Ind_Out_Colourᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Startᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Endᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      --
                      apply And.intro ( by exact Prop_Startᵤ; );           /- := Start Node -/
                      apply And.intro ( by exact Prop_Endᵤ; );             /- := End Node -/
                      apply And.intro ( by exact Prop_Levelᵤ; );           /- := Colours -/
                      apply Exists.intro Colourᵤ;
                      apply Exists.intro Coloursᵤ;
                      apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵤ;
                                           cases Prop_Colourᵤ with
                                           | inl Prop_NBR_Colourᵤ => rewrite [Prop_NBR_Colourᵤ];
                                                                     exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                           | inr Prop_PST_Colourᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                         ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵤ ); );
                      apply And.intro ( by exact Prop_Coloursᵤ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;              /- := IND.END ≠ all_inc.START -/
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;      /- := all_inc.END = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵤᵤ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      --
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by exact Prop_Out_Colᵤ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour dep_out ∈ OUTGOING -/
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colourᵤᵥ := COLLAPSE.Simp_Out_Colour₁ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colourᵤᵥ;
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵤ : all_outᵤ.COLOUR ≠ Colourᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 apply absurd Prop_Colourᵤ;              /- := Colour ∉ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                                                 cases Ind_Out_Colourᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Colour, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_nbrᵤ; )
                                                                                                                                  ( by rewrite [←imp_false];
                                                                                                                                       intro Past_Zero;
                                                                                                                                       simp only [check_numbers] at prop_check_pastᵤ;
                                                                                                                                       cases prop_check_pastᵤ with | intro _ prop_check_pastᵤ =>
                                                                                                                                       apply absurd (prop_check_pastᵤ Past_Zero);
                                                                                                                                       trivial; );
                                                                                                 | inr GT_Zero => rewrite [←EQ_Colour, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₁ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T1_Of_T1.NODES


namespace COVERAGE.T3_Of_T3.NODES
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Collapse Execution (Type 2 & Type 2 => Type 3) (Nodes) -/
  theorem Col_Of_Collapse_Pre_Pre {RULEᵤ RULEᵥ : Neighborhood} :
    ( check_collapse_nodes RULEᵤ RULEᵥ ) →
    ( type3_pre_collapse RULEᵤ ) →
    ( type3_pre_collapse RULEᵥ ) →
    ---------------------------
    ( type3_collapse (collapse RULEᵤ RULEᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  --
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  --
  simp only [type3_pre_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_startsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  --
  cases prop_out_unitᵤ with | intro outᵤ prop_out_unitᵤ =>
  --
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_startsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  --
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  --
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by exact prop_nbrᵤ; );                                        /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvlᵤ; );                                        /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by trivial; );                                                /- := RULE.CENTER.COLLAPSED = true -/
  apply And.intro ( by apply Exists.intro RULEᵥ.CENTER.NUMBER;                    /- := check_numbers (past :: pasts) ∧ RULE.CENTER.PAST = (past::pasts) -/
                       apply Exists.intro RULEᵤ.CENTER.PAST;
                       apply And.intro ( by simp only [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ; );
                       trivial; );
  /- Check Deduction Edges -/
  apply And.intro ( by intro prop_inc_nil;                                        /- := ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];                                                                    /- := RULE.OUTGOING = (out::outs) -/
                       apply Exists.intro ( edge ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )                        /- RULEᵥ.OUTGOING -/
                                                 ( outᵥ.END )
                                                 ( outᵥ.COLOUR )
                                                 ( outᵥ.DEPENDENCY ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )   /- RULEᵤ.OUTGOING -/
                                                                      ( RULEᵤ.OUTGOING ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;                          /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [Deduction.edge.injEq'];
                       --
                       simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colourᵥ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colourᵥ;
                       --
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;                              /- := out₁ = outᵥ -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];                /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             --
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;                 /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Colour₂ᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.COLOUR = 0 ∨ out₂.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₂ᵤ ⊢;
                                                             have NE_Colour : outᵥ.COLOUR ≠ out₂.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Colour, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];                /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;                              /- := out₂ = outᵥ -/
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;                 /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Colour₁ᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.COLOUR = 0 ∨ out₁.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₁ᵤ ⊢;
                                                             have NE_Colour : out₁.COLOUR ≠ outᵥ.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Colour, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];              /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];              /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;               /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.START = RULEᵤ.CENTER -/
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;               /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [Deduction.edge.injEq] at Out_Start₁ᵤ Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ; );
  apply And.intro ( by intro case_hpt;                                /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;                           /- := ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];                /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;            /- := inc ∈ RULEᵥ.INCOMING -/
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;                        /- := type_incoming.check inc RULEᵥ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Startᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Endᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colourᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                            /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵥ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵥ with | intro Colourᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Coloursᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply Exists.intro Colourᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;            /- := inc ∈ RULEᵤ.INCOMING -/
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;                        /- := type_incoming.check inc RULEᵤ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Startᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Endᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colourᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                             /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵤ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵤ with | intro Colourᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Coloursᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply Exists.intro Colourᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;          /- := out ∈ RULEᵥ.OUTGOING -/
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;                      /- := type_outgoing.check out RULEᵥ.CENTER -/
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Startₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Endₕ₁ᵥ Prop_Colourₕ₁ᵥ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );    /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                               /- := End Node -/
                                                                                                                   exact Prop_Endₕ₁ᵥ; );
                                                                                              exact Prop_Colourₕ₁ᵥ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Startᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Endᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colourᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₁ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Startₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Endₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colourₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                                            /- := Type 3 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                         /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                                                    /- := End Node -/
                                                                                                                   exact Prop_Endₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourₕ₃ᵥ;              /- := Colours -/
                                                                                                                   rewrite [Prop_Colourₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                       ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Coloursₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Startᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Endᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colourᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 3 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₃ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Coloursᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;          /- := out ∈ RULEᵤ.OUTGOING -/
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;                      /- := type_outgoing.check out RULEᵤ.CENTER -/
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Startₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Endₕ₁ᵤ Prop_Colourₕ₁ᵤ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₁ᵤ; );                                /- := End Node -/
                                                                                              exact Prop_Colourₕ₁ᵤ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Startᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Endᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colourᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₁ᵤ; );                                                   /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₁ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₁ᵤ => rewrite [Prop_NBR_Colourᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₁ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Startₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Endₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colourₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₃ᵤ; );                                /- := End Node -/
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourₕ₃ᵤ;                  /- := Colours -/
                                                                                                                   cases Prop_Colourₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                   | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                    ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Coloursₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Startᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Endᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colourᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                            /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );   /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₃ᵤ; );                              /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₃ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Coloursᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Startᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Endᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Coloursᵥ Prop_Dir_Outᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Colours -/
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Colour₁ᵥ;
                                           apply Exists.intro Colour₂ᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colour₁ᵥ;
                                                                rewrite [Prop_Colour₁ᵥ];
                                                                exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                    ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                                           apply And.intro ( by exact Prop_Coloursᵥ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Colour₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           --
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by exact Prop_Out_Colᵥ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵥ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    have Dir_Out_Colourᵥᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Dir_Out_Memᵥᵤ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colour₁ᵥ;                               /- := Colour₁ = RULEᵥ.CENTER.NUMBER -/
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have NE_Colourᵥ : all_outᵥ.COLOUR ≠ Colour₁ᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Colour;
                                                                                                                       rewrite [EQ_Colour, Prop_Colour₁ᵥ] at Dir_Out_Colourᵥᵤ;
                                                                                                                       cases Dir_Out_Colourᵥᵤ with
                                                                                                                       | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                                        exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                                       | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by exact prop_ne_pst; );
                                                                    simp only [NE_Colourᵥ, false_and, and_false];
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Startᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Endᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Coloursᵤ Prop_Dir_Outᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                           /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Levelᵤ; );                           /- := Colours -/
                                           apply Exists.intro Colour₁ᵤ;
                                           apply Exists.intro Colour₂ᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colour₁ᵤ;
                                                                cases Prop_Colour₁ᵤ with
                                                                | inl Prop_NBR_Colour₁ᵤ => rewrite [Prop_NBR_Colour₁ᵤ];
                                                                                           exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                | inr Prop_PST_Colour₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                              ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colour₁ᵤ ); );
                                           apply And.intro ( by exact Prop_Coloursᵤ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Colour₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           --
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by exact Prop_Out_Colᵤ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵤ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    have Dir_Out_Colourᵤᵥ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵥ Dir_Out_Memᵤᵥ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Dir_Out_Colourᵤᵥ;
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have NE_Colourᵤ : all_outᵤ.COLOUR ≠ Colour₁ᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Colour;
                                                                                                                       apply absurd Prop_Colour₁ᵤ;              /- := Colour₁ ∉ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                                                                       cases Dir_Out_Colourᵤᵥ with
                                                                                                                       | inl EQ_Zero => rewrite [←EQ_Colour, EQ_Zero, prop_pstᵤ];
                                                                                                                                        rewrite [List.Eq_Iff_Mem_Unit];
                                                                                                                                        exact Nat.ne_of_lt prop_nbrᵤ;
                                                                                                                       | inr GT_Zero => rewrite [←EQ_Colour, GT_Zero];
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by exact prop_ne_pst; );
                                                                    simp only [NE_Colourᵤ, false_and, and_false];
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Startᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Endᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      --
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Start Node -/
                                           exact Prop_Startᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := End Node -/
                                           exact Prop_Endᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Colours -/
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colourᵥ;
                      apply Exists.intro Coloursᵥ;
                      apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;
                                           rewrite [Prop_Colourᵥ];
                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                      apply And.intro ( by exact Prop_Coloursᵥ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;      /- := all_inc.END = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵥᵥ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;              /- := all_inc.START ≠ IND.END -/
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );
                      /- := Check Indirect-Outgoing Duo: -/
                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      --
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by exact Prop_Out_Colᵥ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colourᵥᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;                                /- := Colour = RULEᵥ.CENTER.NUMBER -/
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵥ : all_outᵥ.COLOUR ≠ Colourᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 rewrite [EQ_Colour, Prop_Colourᵥ] at Ind_Out_Colourᵥᵤ;
                                                                                                 cases Ind_Out_Colourᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Startᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Endᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      --
                      apply And.intro ( by exact Prop_Startᵤ; );           /- := Start Node -/
                      apply And.intro ( by exact Prop_Endᵤ; );             /- := End Node -/
                      apply And.intro ( by exact Prop_Levelᵤ; );           /- := Colours -/
                      apply Exists.intro Colourᵤ;
                      apply Exists.intro Coloursᵤ;
                      apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵤ;
                                           cases Prop_Colourᵤ with
                                           | inl Prop_NBR_Colourᵤ => rewrite [Prop_NBR_Colourᵤ];
                                                                     exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                           | inr Prop_PST_Colourᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                         ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵤ ); );
                      apply And.intro ( by exact Prop_Coloursᵤ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;              /- := IND.END ≠ all_inc.START -/
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;      /- := all_inc.END = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵤᵤ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      --
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by exact Prop_Out_Colᵤ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour dep_out ∈ OUTGOING -/
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colourᵤᵥ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colourᵤᵥ;
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵤ : all_outᵤ.COLOUR ≠ Colourᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 apply absurd Prop_Colourᵤ;                /- := Colour ∉ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                                                 cases Ind_Out_Colourᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Colour, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Iff_Mem_Unit];
                                                                                                                  exact Nat.ne_of_lt prop_nbrᵤ;
                                                                                                 | inr GT_Zero => rewrite [←EQ_Colour, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

  /- Lemma: Collapse Execution (Type 3 & Type 2 => Type 3) (Nodes) -/
  theorem Col_Of_Collapse_Col_Pre {RULEᵤ RULEᵥ : Neighborhood} :
    ( check_collapse_nodes RULEᵤ RULEᵥ ) →
    ( type3_collapse RULEᵤ ) →
    ( type3_pre_collapse RULEᵥ ) →
    ---------------------------
    ( type3_collapse (collapse RULEᵤ RULEᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  --
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  --
  simp only [type3_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  --
  cases prop_pstᵤ with | intro pastᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro pastsᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro prop_check_pastᵤ prop_pstᵤ =>
  --
  cases prop_out_consᵤ with | intro outᵤ prop_out_consᵤ =>
  cases prop_out_consᵤ with | intro outsᵤ prop_out_consᵤ =>
  --
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_startsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  --
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  --
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by exact prop_nbrᵤ; );                                        /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvlᵤ; );                                        /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by trivial; );                                                /- := RULE.CENTER.COLLAPSED = true -/
  apply And.intro ( by apply Exists.intro RULEᵥ.CENTER.NUMBER;                    /- := check_numbers (past :: pasts) ∧ RULE.CENTER.PAST = (past::pasts) -/
                       apply Exists.intro RULEᵤ.CENTER.PAST;
                       apply And.intro ( by rewrite [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ prop_check_pastᵤ; );
                       trivial; );
  /- Check Deduction Edges -/
  apply And.intro ( by intro prop_inc_nil;                                        /- := ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];                                                                    /- := RULE.OUTGOING = (out::outs) -/
                       apply Exists.intro ( edge ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )                        /- RULEᵥ.OUTGOING -/
                                                 ( outᵥ.END )
                                                 ( outᵥ.COLOUR )
                                                 ( outᵥ.DEPENDENCY ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )   /- RULEᵤ.OUTGOING -/
                                                                      ( RULEᵤ.OUTGOING ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;                          /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [Deduction.edge.injEq'];
                       --
                       simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colourᵥ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colourᵥ;
                       --
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;                              /- := out₁ = outᵥ -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];                /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             --
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;                 /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Colour₂ᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.COLOUR = 0 ∨ out₂.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₂ᵤ ⊢;
                                                             have NE_Colour : outᵥ.COLOUR ≠ out₂.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Colour, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];                /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;                              /- := out₂ = outᵥ -/
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;                 /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Colour₁ᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.COLOUR = 0 ∨ out₁.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                             --
                                                             simp only [true_and] at gt_zero₁₂ Out_Colour₁ᵤ ⊢;
                                                             have NE_Colour : out₁.COLOUR ≠ outᵥ.COLOUR := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Colour;
                                                                                                              cases Out_Colourᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Colour, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Colour₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Colour, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Colour, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by exact prop_ne_pst; );
                                                             simp only [NE_Colour, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];              /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];              /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;               /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.START = RULEᵤ.CENTER -/
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;               /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [Deduction.edge.injEq] at Out_Start₁ᵤ Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ; );
  apply And.intro ( by intro case_hpt;                                /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;                           /- := ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];                /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;            /- := inc ∈ RULEᵥ.INCOMING -/
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;                        /- := type_incoming.check inc RULEᵥ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Startᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Endᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colourᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                            /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵥ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵥ with | intro Colourᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Coloursᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply Exists.intro Colourᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;            /- := inc ∈ RULEᵤ.INCOMING -/
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;                        /- := type_incoming.check inc RULEᵤ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Startᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Endᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colourᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                             /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵤ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵤ with | intro Colourᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Coloursᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply Exists.intro Colourᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;          /- := out ∈ RULEᵥ.OUTGOING -/
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;                      /- := type_outgoing.check out RULEᵥ.CENTER -/
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Startₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Endₕ₁ᵥ Prop_Colourₕ₁ᵥ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );    /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                               /- := End Node -/
                                                                                                                   exact Prop_Endₕ₁ᵥ; );
                                                                                              exact Prop_Colourₕ₁ᵥ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Startᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Endᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colourᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₁ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Startₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Endₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colourₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                                            /- := Type 3 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                         /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                                                    /- := End Node -/
                                                                                                                   exact Prop_Endₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourₕ₃ᵥ;              /- := Colours -/
                                                                                                                   rewrite [Prop_Colourₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                       ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Coloursₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Startᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Endᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colourᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 3 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₃ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Coloursᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;          /- := out ∈ RULEᵤ.OUTGOING -/
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;                      /- := type_outgoing.check out RULEᵤ.CENTER -/
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Startₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Endₕ₁ᵤ Prop_Colourₕ₁ᵤ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₁ᵤ; );                                /- := End Node -/
                                                                                              exact Prop_Colourₕ₁ᵤ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Startᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Endᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colourᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₁ᵤ; );                                                   /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₁ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₁ᵤ => rewrite [Prop_NBR_Colourᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₁ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Startₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Endₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colourₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₃ᵤ; );                                /- := End Node -/
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourₕ₃ᵤ;                  /- := Colours -/
                                                                                                                   cases Prop_Colourₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                   | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                    ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Coloursₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Startᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Endᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colourᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                            /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );   /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₃ᵤ; );                              /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₃ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Coloursᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Startᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Endᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Coloursᵥ Prop_Dir_Outᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Colours -/
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Colour₁ᵥ;
                                           apply Exists.intro Colour₂ᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colour₁ᵥ;
                                                                rewrite [Prop_Colour₁ᵥ];
                                                                exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                    ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                                           apply And.intro ( by exact Prop_Coloursᵥ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Colour₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           --
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by exact Prop_Out_Colᵥ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵥ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    have Dir_Out_Colourᵥᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Dir_Out_Memᵥᵤ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colour₁ᵥ;                               /- := Colour₁ = RULEᵥ.CENTER.NUMBER -/
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have NE_Colourᵥ : all_outᵥ.COLOUR ≠ Colour₁ᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Colour;
                                                                                                                       rewrite [EQ_Colour, Prop_Colour₁ᵥ] at Dir_Out_Colourᵥᵤ;
                                                                                                                       cases Dir_Out_Colourᵥᵤ with
                                                                                                                       | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                                        exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                                       | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by exact prop_ne_pst; );
                                                                    simp only [NE_Colourᵥ, false_and, and_false];
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Startᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Endᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Coloursᵤ Prop_Dir_Outᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                           /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Levelᵤ; );                           /- := Colours -/
                                           apply Exists.intro Colour₁ᵤ;
                                           apply Exists.intro Colour₂ᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colour₁ᵤ;
                                                                cases Prop_Colour₁ᵤ with
                                                                | inl Prop_NBR_Colour₁ᵤ => rewrite [Prop_NBR_Colour₁ᵤ];
                                                                                           exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                | inr Prop_PST_Colour₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                               ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colour₁ᵤ ); );
                                           apply And.intro ( by exact Prop_Coloursᵤ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Colour₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           --
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by exact Prop_Out_Colᵤ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵤ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    have Dir_Out_Colourᵤᵥ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵥ Dir_Out_Memᵤᵥ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Dir_Out_Colourᵤᵥ;
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have NE_Colourᵤ : all_outᵤ.COLOUR ≠ Colour₁ᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Colour;
                                                                                                                       apply absurd Prop_Colour₁ᵤ;              /- := Colour₁ ∉ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                                                                       cases Dir_Out_Colourᵤᵥ with
                                                                                                                       | inl EQ_Zero => rewrite [←EQ_Colour, EQ_Zero, prop_pstᵤ];
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_nbrᵤ; )
                                                                                                                                                        ( by rewrite [←imp_false];
                                                                                                                                                             intro Past_Zero;
                                                                                                                                                             simp only [check_numbers] at prop_check_pastᵤ;
                                                                                                                                                             cases prop_check_pastᵤ with | intro _ prop_check_pastᵤ =>
                                                                                                                                                             apply absurd (prop_check_pastᵤ Past_Zero);
                                                                                                                                                             trivial; );
                                                                                                                       | inr GT_Zero => rewrite [←EQ_Colour, GT_Zero];
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by exact prop_ne_pst; );
                                                                    simp only [NE_Colourᵤ, false_and, and_false];
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Startᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Endᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      --
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Start Node -/
                                           exact Prop_Startᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := End Node -/
                                           exact Prop_Endᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Colours -/
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colourᵥ;
                      apply Exists.intro Coloursᵥ;
                      apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;
                                           rewrite [Prop_Colourᵥ];
                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                      apply And.intro ( by exact Prop_Coloursᵥ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;      /- := all_inc.END = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵥᵥ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;              /- := all_inc.START ≠ IND.END -/
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );
                      /- := Check Indirect-Outgoing Duo: -/
                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      --
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by exact Prop_Out_Colᵥ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colourᵥᵤ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;                                /- := Colour = RULEᵥ.CENTER.NUMBER -/
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵥ : all_outᵥ.COLOUR ≠ Colourᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 rewrite [EQ_Colour, Prop_Colourᵥ] at Ind_Out_Colourᵥᵤ;
                                                                                                 cases Ind_Out_Colourᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Startᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Endᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      --
                      apply And.intro ( by exact Prop_Startᵤ; );           /- := Start Node -/
                      apply And.intro ( by exact Prop_Endᵤ; );             /- := End Node -/
                      apply And.intro ( by exact Prop_Levelᵤ; );           /- := Colours -/
                      apply Exists.intro Colourᵤ;
                      apply Exists.intro Coloursᵤ;
                      apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵤ;
                                           cases Prop_Colourᵤ with
                                           | inl Prop_NBR_Colourᵤ => rewrite [Prop_NBR_Colourᵤ];
                                                                     exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                           | inr Prop_PST_Colourᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                         ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵤ ); );
                      apply And.intro ( by exact Prop_Coloursᵤ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;              /- := IND.END ≠ all_inc.START -/
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;      /- := all_inc.END = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵤᵤ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      --
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by exact Prop_Out_Colᵤ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour dep_out ∈ OUTGOING -/
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colourᵤᵥ := COLLAPSE.Simp_Out_Colour₃ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);          /- := all_out.COLOUR = 0 ∨ all_out.COLOUR ∈ RULEᵥ.CENTER.NUMBER :: RULEᵥ.CENTER.PAST -/
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colourᵤᵥ;
                                               rewrite [Deduction.edge.injEq];
                                               have NE_Colourᵤ : all_outᵤ.COLOUR ≠ Colourᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Colour;
                                                                                                 apply absurd Prop_Colourᵤ;              /- := Colour ∉ RULEᵤ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST -/
                                                                                                 cases Ind_Out_Colourᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Colour, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_nbrᵤ; )
                                                                                                                                  ( by rewrite [←imp_false];
                                                                                                                                       intro Past_Zero;
                                                                                                                                       simp only [check_numbers] at prop_check_pastᵤ;
                                                                                                                                       cases prop_check_pastᵤ with | intro _ prop_check_pastᵤ =>
                                                                                                                                       apply absurd (prop_check_pastᵤ Past_Zero);
                                                                                                                                       trivial; );
                                                                                                 | inr GT_Zero => rewrite [←EQ_Colour, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by exact prop_ne_pst; );
                                               simp only [NE_Colourᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T3_Of_T3.NODES


namespace COVERAGE.T3_Of_T3.EDGES
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Collapse Execution (Type 2 & Type 3 => Type 3) (Nodes & Edges) -/
  theorem Col_Of_Collapse_Pre_Pre {RULEᵤ RULEᵥ : Neighborhood} :
    ( check_collapse_edges RULEᵤ RULEᵥ ) →
    ( type3_pre_collapse RULEᵤ ) →
    ( type3_pre_collapse RULEᵥ ) →
    ---------------------------
    ( type3_collapse (collapse RULEᵤ RULEᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  --
  simp only [check_collapse_edges] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_eq_out prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  --
  cases prop_eq_out with | intro eq_outᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_outᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_colourᵤ prop_eq_out =>
  --
  simp only [type3_pre_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_startsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  --
  cases prop_out_unitᵤ with | intro outᵤ prop_out_unitᵤ =>
  --
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_startsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  --
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  --
  rewrite [prop_out_unitᵥ] at eq_out_memᵥ;
  simp only [List.Eq_Iff_Mem_Unit] at eq_out_memᵥ;
  simp only [eq_out_memᵥ] at prop_eq_out;
  cases prop_eq_out with | intro prop_eq_out_end prop_eq_out =>
  cases prop_eq_out with | intro prop_eq_out_colour prop_eq_out_dependency =>
  --
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by exact prop_nbrᵤ; );                                        /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvlᵤ; );                                        /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by trivial; );                                                /- := RULE.CENTER.COLLAPSED = true -/
  apply And.intro ( by apply Exists.intro RULEᵥ.CENTER.NUMBER;                    /- := check_numbers (past :: pasts) ∧ RULE.CENTER.PAST = (past::pasts) -/
                       apply Exists.intro RULEᵤ.CENTER.PAST;
                       apply And.intro ( by simp only [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ; );
                       trivial; );
  /- Check Deduction Edges -/
  apply And.intro ( by intro prop_inc_nil;                                        /- := ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];                                                                    /- := RULE.OUTGOING = (out::outs) -/
                       apply Exists.intro ( edge ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )                        /- RULEᵥ.OUTGOING -/
                                                 ( outᵥ.END )
                                                 ( outᵥ.COLOUR )
                                                 ( outᵥ.DEPENDENCY ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )   /- RULEᵤ.OUTGOING -/
                                                                      ( RULEᵤ.OUTGOING ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;                          /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [Deduction.edge.injEq'];
                       --
                       simp only [type_outgoing₃] at prop_outgoingᵤ;
                       have Eq_Out_Colourᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ eq_out_memᵤ);
                       --
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ, REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];                 /- := out₁ = outᵥ, out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency, true_and];
                                                             --
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;                 /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₂ᵤ);     /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ eq_out_memᵤ Out_Mem₂ᵤ (Or.inl eq_out_colourᵤ);
                                                             simp only [Deduction.edge.injEq'] at Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Eq_Out_Colourᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ;
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ, out_mem₂ᵥ];                 /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER, out₂ = outᵥ -/
                                                             simp only [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency, true_and];
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;                 /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₁ᵤ);     /- := out₁.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ eq_out_memᵤ (Or.inr eq_out_colourᵤ);
                                                             simp only [Deduction.edge.injEq'] at Out_Start₁ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Eq_Out_Colourᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ;
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];              /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];              /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [true_and];
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;               /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.START = RULEᵤ.CENTER -/
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;               /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [Deduction.edge.injEq] at Out_Start₁ᵤ Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ; );
  apply And.intro ( by intro case_hpt;                                /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;                           /- := ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];                /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;            /- := inc ∈ RULEᵥ.INCOMING -/
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;                        /- := type_incoming.check inc RULEᵥ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Startᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Endᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colourᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                            /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵥ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵥ with | intro Colourᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Coloursᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply Exists.intro Colourᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;            /- := inc ∈ RULEᵤ.INCOMING -/
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;                        /- := type_incoming.check inc RULEᵤ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Startᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Endᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colourᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                             /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵤ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵤ with | intro Colourᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Coloursᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply Exists.intro Colourᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;          /- := out ∈ RULEᵥ.OUTGOING -/
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;                      /- := type_outgoing.check out RULEᵥ.CENTER -/
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Startₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Endₕ₁ᵥ Prop_Colourₕ₁ᵥ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );    /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                               /- := End Node -/
                                                                                                                   exact Prop_Endₕ₁ᵥ; );
                                                                                              exact Prop_Colourₕ₁ᵥ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Startᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Endᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colourᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₁ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Startₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Endₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colourₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                                            /- := Type 3 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                         /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                                                    /- := End Node -/
                                                                                                                   exact Prop_Endₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourₕ₃ᵥ;              /- := Colours -/
                                                                                                                   rewrite [Prop_Colourₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                       ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Coloursₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Startᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Endᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colourᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 3 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₃ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Coloursᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;          /- := out ∈ RULEᵤ.OUTGOING -/
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;                      /- := type_outgoing.check out RULEᵤ.CENTER -/
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Startₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Endₕ₁ᵤ Prop_Colourₕ₁ᵤ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₁ᵤ; );                                /- := End Node -/
                                                                                              exact Prop_Colourₕ₁ᵤ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Startᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Endᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colourᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₁ᵤ; );                                                   /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₁ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₁ᵤ => rewrite [Prop_NBR_Colourᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₁ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Startₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Endₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colourₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₃ᵤ; );                                /- := End Node -/
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourₕ₃ᵤ;                  /- := Colours -/
                                                                                                                   cases Prop_Colourₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                   | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                    ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Coloursₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Startᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Endᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colourᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                            /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );   /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₃ᵤ; );                              /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₃ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Coloursᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Startᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Endᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Coloursᵥ Prop_Dir_Outᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Colours -/
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Colour₁ᵥ;
                                           apply Exists.intro Colour₂ᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colour₁ᵥ;
                                                                rewrite [Prop_Colour₁ᵥ];
                                                                exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                    ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                                           apply And.intro ( by exact Prop_Coloursᵥ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Colour₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           --
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by exact Prop_Out_Colᵥ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵥ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    --
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    --
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    --
                                                                    have Prop_All_Outᵤ := prop_out_coloursᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ ⊢;
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    --
                                                                    rewrite [prop_out_unitᵥ] at Prop_Dir_Outᵥ;
                                                                    simp only [List.Eq_Iff_Mem_Unit] at Prop_Dir_Outᵥ;
                                                                    simp only [←Prop_Dir_Outᵥ] at prop_eq_out_end prop_eq_out_colour prop_eq_out_dependency;
                                                                    rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                                                    --
                                                                    exact Iff.intro ( by intro iff_eq_colourᵥᵤ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colourᵥᵤ;
                                                                                         simp only [iff_eq_colourᵥᵤ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵥᵤ;
                                                                                         simp only [iff_eq_edgeᵥᵤ]; );
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Startᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Endᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Coloursᵤ Prop_Dir_Outᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                           /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Levelᵤ; );                           /- := Colours -/
                                           apply Exists.intro Colour₁ᵤ;
                                           apply Exists.intro Colour₂ᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colour₁ᵤ;
                                                                cases Prop_Colour₁ᵤ with
                                                                | inl Prop_NBR_Colour₁ᵤ => rewrite [Prop_NBR_Colour₁ᵤ];
                                                                                           exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                | inr Prop_PST_Colour₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                              ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colour₁ᵤ ); );
                                           apply And.intro ( by exact Prop_Coloursᵤ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Colour₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           --
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by exact Prop_Out_Colᵤ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵤ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [Deduction.edge.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Startᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Endᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colourᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                                                    rewrite [Dir_Out_Endᵤᵥ, Dir_Out_Colourᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                                                    rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                                                    --
                                                                    have Prop_All_Outᵤ := prop_out_coloursᵤ eq_out_memᵤ Prop_Dir_Outᵤ (Or.inl eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ;
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    --
                                                                    exact Iff.intro ( by intro iff_eq_colourᵤᵥ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colourᵤᵥ;
                                                                                         simp only [iff_eq_colourᵤᵥ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵤᵥ;
                                                                                         simp only [iff_eq_edgeᵤᵥ]; );
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Startᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Endᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      --
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Start Node -/
                                           exact Prop_Startᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := End Node -/
                                           exact Prop_Endᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Colours -/
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colourᵥ;
                      apply Exists.intro Coloursᵥ;
                      apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;
                                           rewrite [Prop_Colourᵥ];
                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                      apply And.intro ( by exact Prop_Coloursᵥ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;      /- := all_inc.END = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵥᵥ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;              /- := all_inc.START ≠ IND.END -/
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );
                      /- := Check Indirect-Outgoing Duo: -/
                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      --
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by exact Prop_Out_Colᵥ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                               --
                                               have Prop_All_Outᵤ := prop_out_coloursᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ ⊢;
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               --
                                               rewrite [prop_out_unitᵥ] at Prop_Ind_Outᵥ;
                                               simp only [List.Eq_Iff_Mem_Unit] at Prop_Ind_Outᵥ;
                                               simp only [←Prop_Ind_Outᵥ] at prop_eq_out_end prop_eq_out_colour prop_eq_out_dependency;
                                               rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                               --
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               exact Iff.intro ( by intro iff_eq_colourᵥᵤ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colourᵥᵤ;
                                                                    simp only [iff_eq_colourᵥᵤ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵥᵤ;
                                                                    simp only [iff_eq_edgeᵥᵤ]; );
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Startᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Endᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      --
                      apply And.intro ( by exact Prop_Startᵤ; );           /- := Start Node -/
                      apply And.intro ( by exact Prop_Endᵤ; );             /- := End Node -/
                      apply And.intro ( by exact Prop_Levelᵤ; );           /- := Colours -/
                      apply Exists.intro Colourᵤ;
                      apply Exists.intro Coloursᵤ;
                      apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵤ;
                                           cases Prop_Colourᵤ with
                                           | inl Prop_NBR_Colourᵤ => rewrite [Prop_NBR_Colourᵤ];
                                                                     exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                           | inr Prop_PST_Colourᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                         ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵤ ); );
                      apply And.intro ( by exact Prop_Coloursᵤ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;              /- := IND.END ≠ all_inc.START -/
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;      /- := all_inc.END = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵤᵤ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      --
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by exact Prop_Out_Colᵤ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour dep_out ∈ OUTGOING -/
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                               rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                               rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                               rewrite [Deduction.edge.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Startᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Endᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colourᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                               rewrite [Dir_Out_Endᵤᵥ, Dir_Out_Colourᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                               rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                               --
                                               have Prop_All_Outᵤ := prop_out_coloursᵤ eq_out_memᵤ Prop_Ind_Outᵤ (Or.inl eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ;
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               --
                                               exact Iff.intro ( by intro iff_eq_colourᵤᵥ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colourᵤᵥ;
                                                                    simp only [iff_eq_colourᵤᵥ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵤᵥ;
                                                                    simp only [iff_eq_edgeᵤᵥ]; );
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

  /- Lemma: Collapse Execution (Type 3 & Type 2 => Type 3) (Nodes & Edges) -/
  theorem Col_Of_Collapse_Col_Pre {RULEᵤ RULEᵥ : Neighborhood} :
    ( check_collapse_edges RULEᵤ RULEᵥ ) →
    ( type3_collapse RULEᵤ ) →
    ( type3_pre_collapse RULEᵥ ) →
    ---------------------------
    ( type3_collapse (collapse RULEᵤ RULEᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  --
  simp only [check_collapse_edges] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_eq_out prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  --
  cases prop_eq_out with | intro eq_outᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_outᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_colourᵤ prop_eq_out =>
  --
  simp only [type3_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_coloursᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  --
  cases prop_pstᵤ with | intro pastᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro pastsᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro prop_check_pastᵤ prop_pstᵤ =>
  --
  cases prop_out_consᵤ with | intro outᵤ prop_out_consᵤ =>
  cases prop_out_consᵤ with | intro outsᵤ prop_out_consᵤ =>
  --
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_coloursᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_startsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  --
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  --
  rewrite [prop_out_unitᵥ] at eq_out_memᵥ;
  simp only [List.Eq_Iff_Mem_Unit] at eq_out_memᵥ;
  simp only [eq_out_memᵥ] at prop_eq_out;
  cases prop_eq_out with | intro prop_eq_out_end prop_eq_out =>
  cases prop_eq_out with | intro prop_eq_out_colour prop_eq_out_dependency =>
  --
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by exact prop_nbrᵤ; );                                        /- := RULE.CENTER.NUMBER > 0 -/
  apply And.intro ( by exact prop_lvlᵤ; );                                        /- := RULE.CENTER.LEVEL > 0 -/
  apply And.intro ( by trivial; );                                                /- := RULE.CENTER.COLLAPSED = true -/
  apply And.intro ( by apply Exists.intro RULEᵥ.CENTER.NUMBER;                    /- := check_numbers (past :: pasts) ∧ RULE.CENTER.PAST = (past::pasts) -/
                       apply Exists.intro RULEᵤ.CENTER.PAST;
                       apply And.intro ( by rewrite [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ prop_check_pastᵤ; );
                       trivial; );
  /- Check Deduction Edges -/
  apply And.intro ( by intro prop_inc_nil;                                        /- := ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];                                                                    /- := RULE.OUTGOING = (out::outs) -/
                       apply Exists.intro ( edge ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )                        /- RULEᵥ.OUTGOING -/
                                                 ( outᵥ.END )
                                                 ( outᵥ.COLOUR )
                                                 ( outᵥ.DEPENDENCY ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )   /- RULEᵤ.OUTGOING -/
                                                                      ( RULEᵤ.OUTGOING ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;                          /- := OUT₁.COLOUR = OUT₂.COLOUR ↔ OUT₁ = OUT₂ -/
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [Deduction.edge.injEq'];
                       --
                       simp only [type_outgoing₃] at prop_outgoingᵤ;
                       have Eq_Out_Colourᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ eq_out_memᵤ);
                       --
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ, REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];                 /- := out₁ = outᵥ, out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency, true_and];
                                                             --
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;                 /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₂ᵤ);     /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ eq_out_memᵤ Out_Mem₂ᵤ (Or.inl eq_out_colourᵤ);
                                                             simp only [Deduction.edge.injEq'] at Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Eq_Out_Colourᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ;
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ, out_mem₂ᵥ];                 /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER, out₂ = outᵥ -/
                                                             simp only [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency, true_and];
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;                 /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₁ᵤ);     /- := out₁.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ eq_out_memᵤ (Or.inr eq_out_colourᵤ);
                                                             simp only [Deduction.edge.injEq'] at Out_Start₁ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Eq_Out_Colourᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ;
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Start_RwOutgoing out_mem₁ᵤ];              /- := out₁.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             rewrite [REWRITE.Get_Start_RwOutgoing out_mem₂ᵤ];              /- := out₂.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                             simp only [true_and];
                                                             --
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;               /- := out₁ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Start₁ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₁ᵤ);   /- := out₁.START = RULEᵤ.CENTER -/
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;               /- := out₂ ∈ RULEᵥ.OUTGOING -/
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Start₂ᵤ := COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Out_Mem₂ᵤ);   /- := out₂.START = RULEᵤ.CENTER -/
                                                             --
                                                             have Iff_Out_Colourᵤ := prop_out_coloursᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [Deduction.edge.injEq] at Out_Start₁ᵤ Out_Start₂ᵤ Iff_Out_Colourᵤ;
                                                             simp only [Out_Start₁ᵤ, Out_Start₂ᵤ, true_and] at Iff_Out_Colourᵤ;
                                                             exact Iff_Out_Colourᵤ; );
  apply And.intro ( by intro case_hpt;                                /- := ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) -/
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;                           /- := ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) -/
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];                /- := List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) -/
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Incoming Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;            /- := inc ∈ RULEᵥ.INCOMING -/
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;                        /- := type_incoming.check inc RULEᵥ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Startᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Endᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colourᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                            /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵥ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵥ with | intro Colourᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Coloursᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           --
                                           apply Exists.intro Colourᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;            /- := inc ∈ RULEᵤ.INCOMING -/
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;                        /- := type_incoming.check inc RULEᵤ.CENTER -/
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Startᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Endᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colourᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                             /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwIncoming inc_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Colourᵤ; );                            /- := Colours -/
                                           /- := Check Incoming-Indirect Duo: -/
                                           cases Prop_Inc_Indᵤ with | intro Colourᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Coloursᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           --
                                           apply Exists.intro Colourᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                 /- := path anc INC.START (0::colour::colours) ∈ INDIRECT -/
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Outgoing Edges -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;          /- := out ∈ RULEᵥ.OUTGOING -/
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;                      /- := type_outgoing.check out RULEᵥ.CENTER -/
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Startₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Endₕ₁ᵥ Prop_Colourₕ₁ᵥ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );    /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                               /- := End Node -/
                                                                                                                   exact Prop_Endₕ₁ᵥ; );
                                                                                              exact Prop_Colourₕ₁ᵥ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Startᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Endᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colourᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₁ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Startₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Endₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colourₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                                            /- := Type 3 Hypothesis -/
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                         /- := Start Node -/
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];                                                    /- := End Node -/
                                                                                                                   exact Prop_Endₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourₕ₃ᵥ;              /- := Colours -/
                                                                                                                   rewrite [Prop_Colourₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                       ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Coloursₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Startᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Endᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colourᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 3 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵥ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];                                                   /- := End Node -/
                                                                                                                    exact Prop_Endᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵢₑ₃ᵥ;            /- := Colours -/
                                                                                                                    rewrite [Prop_Colourᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                        ( List.Mem.head RULEᵤ.CENTER.PAST ) );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Coloursᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;          /- := out ∈ RULEᵤ.OUTGOING -/
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;                      /- := type_outgoing.check out RULEᵤ.CENTER -/
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Startₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Endₕ₁ᵤ Prop_Colourₕ₁ᵤ =>
                                                                                              --
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₁ᵤ; );                                /- := End Node -/
                                                                                              exact Prop_Colourₕ₁ᵤ;                                                     /- := Colours -/
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Startᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Endᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colourᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                                                 /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );                        /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₁ᵤ; );                                                   /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₁ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₁ᵤ => rewrite [Prop_NBR_Colourᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₁ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT -/
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Startₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Endₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colourₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];                       /- := Type 1 Hypothesis -/
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );    /- := Start Node -/
                                                                                              apply And.intro ( by exact Prop_Endₕ₃ᵤ; );                                /- := End Node -/
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourₕ₃ᵤ;                  /- := Colours -/
                                                                                                                   cases Prop_Colourₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                   | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                    ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                              /- := Check Outgoing-Direct Duo: -/
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Coloursₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              --
                                                                                              apply Exists.intro Coloursₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                    /- := path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT -/
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Startᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Endᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colourᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );                            /- := Type 1 Introduction & Elimination -/
                                                                                               apply And.intro ( by exact REWRITE.Get_Start_RwOutgoing out_casesᵤ; );   /- := Start Node -/
                                                                                               apply And.intro ( by exact Prop_Endᵢₑ₃ᵤ; );                              /- := End Node -/
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵢₑ₃ᵤ;                /- := Colours -/
                                                                                                                    cases Prop_Colourᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colourᵢₑ₃ᵤ => rewrite [Prop_NBR_Colourᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                                                                    | inr Prop_PST_Colourᵢₑ₃ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                                                                                     ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵢₑ₃ᵤ ); );
                                                                                               /- := Check Outgoing-Indirect Duo: -/
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Coloursᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               --
                                                                                               apply Exists.intro Coloursᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];                   /- := path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT -/
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Direct Paths -/--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Startᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Endᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colour₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Coloursᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colour₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Coloursᵥ Prop_Dir_Outᵥ =>
                                           --
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Start Node -/
                                                                exact Prop_Startᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵥ; );   /- := End Node -/
                                           apply And.intro ( by rewrite [prop_eq_lvl];                          /- := Colours -/
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Colour₁ᵥ;
                                           apply Exists.intro Colour₂ᵥ;
                                           apply Exists.intro Coloursᵥ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colour₁ᵥ;
                                                                rewrite [Prop_Colour₁ᵥ];
                                                                exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                    ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                                           apply And.intro ( by exact Prop_Coloursᵥ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Colour₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           --
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by exact Prop_Out_Colᵥ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵥ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    --
                                                                    have Prop_All_Outᵤ := prop_out_coloursᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ ⊢;
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    --
                                                                    rewrite [prop_out_unitᵥ] at Prop_Dir_Outᵥ;
                                                                    simp only [List.Eq_Iff_Mem_Unit] at Prop_Dir_Outᵥ;
                                                                    simp only [←Prop_Dir_Outᵥ] at prop_eq_out_end prop_eq_out_colour prop_eq_out_dependency;
                                                                    rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                                                    --
                                                                    exact Iff.intro ( by intro iff_eq_colourᵥᵤ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colourᵥᵤ;
                                                                                         simp only [iff_eq_colourᵥᵤ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵥᵤ;
                                                                                         simp only [iff_eq_edgeᵥᵤ]; );
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Startᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Endᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colour₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Coloursᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colour₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Coloursᵤ Prop_Dir_Outᵤ =>
                                           --
                                           apply And.intro ( by exact Prop_Startᵤ; );                           /- := Start Node -/
                                           apply And.intro ( by exact REWRITE.Get_End_RwDirect dir_casesᵤ; );   /- := End Node -/
                                           apply And.intro ( by exact Prop_Levelᵤ; );                           /- := Colours -/
                                           apply Exists.intro Colour₁ᵤ;
                                           apply Exists.intro Colour₂ᵤ;
                                           apply Exists.intro Coloursᵤ;
                                           apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colour₁ᵤ;
                                                                cases Prop_Colour₁ᵤ with
                                                                | inl Prop_NBR_Colour₁ᵤ => rewrite [Prop_NBR_Colour₁ᵤ];
                                                                                           exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                                                | inr Prop_PST_Colour₁ᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                                               ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colour₁ᵤ ); );
                                           apply And.intro ( by exact Prop_Coloursᵤ; );
                                           /- := Check Direct-Outgoing Duo: -/
                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Colour₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           --
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by exact Prop_Out_Colᵤ; );
                                           apply And.intro ( by exact Prop_Colour₂ᵤ; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [Deduction.edge.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Startᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Endᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colourᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                                                    rewrite [Dir_Out_Endᵤᵥ, Dir_Out_Colourᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                                                    rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                                                    --
                                                                    have Prop_All_Outᵤ := prop_out_coloursᵤ eq_out_memᵤ Prop_Dir_Outᵤ (Or.inl eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ;
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    --
                                                                    exact Iff.intro ( by intro iff_eq_colourᵤᵥ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colourᵤᵥ;
                                                                                         simp only [iff_eq_colourᵤᵥ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵤᵥ;
                                                                                         simp only [iff_eq_edgeᵤᵥ]; );
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour₁ ↔ all_out = edge CENTER out Colour₁ dep_out -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  /- Indirect Paths -/------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Startᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Endᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colourᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Coloursᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      --
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Start Node -/
                                           exact Prop_Startᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := End Node -/
                                           exact Prop_Endᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];         /- := Colours -/
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colourᵥ;
                      apply Exists.intro Coloursᵥ;
                      apply And.intro ( by exact Prop_Check_Coloursᵥ; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colourᵥ;
                                           rewrite [Prop_Colourᵥ];
                                           exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                               ( List.Mem.head RULEᵤ.CENTER.PAST ); );
                      apply And.intro ( by exact Prop_Coloursᵥ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;      /- := all_inc.END = RULEᵥ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵥᵥ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;              /- := all_inc.START ≠ IND.END -/
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );
                      /- := Check Indirect-Outgoing Duo: -/
                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      --
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by exact Prop_Out_Colᵥ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour₁ dep_out ∈ OUTGOING -/
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;                                       /- := all_out.COLOUR = colour₁ ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;   /- := all_out.START = RULEᵥ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                               --
                                               have Prop_All_Outᵤ := prop_out_coloursᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ ⊢;
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵥᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               --
                                               rewrite [prop_out_unitᵥ] at Prop_Ind_Outᵥ;
                                               simp only [List.Eq_Iff_Mem_Unit] at Prop_Ind_Outᵥ;
                                               simp only [←Prop_Ind_Outᵥ] at prop_eq_out_end prop_eq_out_colour prop_eq_out_dependency;
                                               rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                               --
                                               exact Iff.intro ( by intro iff_eq_colourᵥᵤ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colourᵥᵤ;
                                                                    simp only [iff_eq_colourᵥᵤ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵥᵤ;
                                                                    simp only [iff_eq_edgeᵥᵤ]; );
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Startᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Endᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colourᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Coloursᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      --
                      apply And.intro ( by exact Prop_Startᵤ; );           /- := Start Node -/
                      apply And.intro ( by exact Prop_Endᵤ; );             /- := End Node -/
                      apply And.intro ( by exact Prop_Levelᵤ; );           /- := Colours -/
                      apply Exists.intro Colourᵤ;
                      apply Exists.intro Coloursᵤ;
                      apply And.intro ( by exact Prop_Check_Coloursᵤ; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colourᵤ;
                                           cases Prop_Colourᵤ with
                                           | inl Prop_NBR_Colourᵤ => rewrite [Prop_NBR_Colourᵤ];
                                                                     exact List.Mem.head ( RULEᵥ.CENTER.NUMBER :: RULEᵤ.CENTER.PAST );
                                           | inr Prop_PST_Colourᵤ => exact List.Mem.tail ( RULEᵤ.CENTER.NUMBER )
                                                                                         ( List.Mem.tail RULEᵥ.CENTER.NUMBER Prop_PST_Colourᵤ ); );
                      apply And.intro ( by exact Prop_Coloursᵤ; );
                      /- := Check Indirect-Incoming Duo: -/
                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      --
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];   /- := edge IND.END CENTER 0 dep_inc ∈ INCOMING -/
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;                                     /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;                      /- := all_inc ∈ RULEᵥ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [Deduction.edge.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;              /- := IND.END ≠ all_inc.START -/
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;                      /- := all_inc ∈ RULEᵤ.INCOMING -/
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;                                 /- := all_inc.START = IND.END ↔ all_inc = edge IND.END CENTER 0 dep_inc -/
                                                                    rewrite [Deduction.edge.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_End (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;      /- := all_inc.END = RULEᵤ.CENTER -/
                                                                    rewrite [←REWRITE.Get_End_RwIncoming all_inc_casesᵤᵤ];                                      /- := all_inc.END = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      --
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by exact Prop_Out_Colᵤ; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];     /- := edge CENTER out colour dep_out ∈ OUTGOING -/
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;                                       /- := all_out.COLOUR = colour ↔ all_out = edge CENTER out colour₁ dep_out -/
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;                      /- := all_out ∈ RULEᵥ.OUTGOING -/
                                               cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                               rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                               rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                               rewrite [Deduction.edge.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Startᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Endᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colourᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                               rewrite [Dir_Out_Endᵤᵥ, Dir_Out_Colourᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                               rewrite [prop_eq_out_end, prop_eq_out_colour, prop_eq_out_dependency];
                                               --
                                               have Prop_All_Outᵤ := prop_out_coloursᵤ eq_out_memᵤ Prop_Ind_Outᵤ (Or.inl eq_out_colourᵤ);  /- := all_out.COLOUR = eq_out.COLOUR ↔ all_out = eq_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Outᵤ;
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵥ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               --
                                               exact Iff.intro ( by intro iff_eq_colourᵤᵥ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colourᵤᵥ;
                                                                    simp only [iff_eq_colourᵤᵥ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵤᵥ;
                                                                    simp only [iff_eq_edgeᵤᵥ]; );
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;                      /- := all_out ∈ RULEᵤ.OUTGOING -/
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;                                 /- := all_out.COLOUR = Colour ↔ all_out = edge CENTER out Colour dep_out -/
                                               rewrite [Deduction.edge.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Start₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;   /- := all_out.START = RULEᵤ.CENTER -/
                                               rewrite [←REWRITE.Get_Start_RwOutgoing all_out_casesᵤᵤ];                                    /- := all_out.START = collapse.center RULEᵤ.CENTER RULEᵥ.CENTER -/
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.T3_Of_T3.EDGES


namespace COVERAGE.R00.NODES
  /- R0E0E: Type0 ⊇-Elimination = Type0 ⊇-Elimination -/
  theorem Coverage_R0E0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_elimination (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0I0E: Type0 ⊇-Introduction = Type0 ⊇-Elimination -/
  theorem Coverage_R0I0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_introduction (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0H0E: Type0 Hypothesis = Type0 ⊇-Elimination -/
  theorem Coverage_R0H0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_hypothesis (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0E0I: Type0 ⊇-Elimination = Type0 ⊇-Introduction -/
  theorem Coverage_R0E0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_elimination (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0I0I: Type0 ⊇-Introduction = Type0 ⊇-Introduction -/
  theorem Coverage_R0I0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_introduction (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0I0H: Type0 Hypothesis = Type0 ⊇-Introduction -/
  theorem Coverage_R0H0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_hypothesis (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0E0H: Type0 ⊇-Elimination = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0E0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_elimination (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0I0H: Type0 ⊇-Introduction = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0I0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_introduction (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0H0H: Type0 Hypothesis = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R0H0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_hypothesis (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R00.NODES

namespace COVERAGE.R02.NODES
  /- R0E0E: Type0 ⊇-Elimination = Type2 ⊇-Elimination -/
  theorem Coverage_R0E2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_elimination (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0I0E: Type0 ⊇-Introduction = Type2 ⊇-Elimination -/
  theorem Coverage_R0I2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_introduction (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0H0E: Type0 Hypothesis = Type2 ⊇-Elimination -/
  theorem Coverage_R0H2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_hypothesis (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0E0I: Type0 ⊇-Elimination = Type2 ⊇-Introduction -/
  theorem Coverage_R0E2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_elimination (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0I0I: Type0 ⊇-Introduction = Type2 ⊇-Introduction -/
  theorem Coverage_R0I2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_introduction (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0H0I: Type0 Hypothesis = Type2 Introduction -/
  theorem Coverage_R0H2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_hypothesis (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0E0H: Type0 ⊇-Elimination = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0E2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_elimination (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0I0H: Type0 ⊇-Introduction = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0I2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_introduction (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R0H0H: Type0 Hypothesis = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R0H2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type0_hypothesis (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R02.NODES

namespace COVERAGE.R20.NODES
  /- R2E0E: Type2 ⊇-Elimination = Type0 ⊇-Elimination -/
  theorem Coverage_R2E0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I0E: Type2 ⊇-Introduction = Type0 ⊇-Elimination -/
  theorem Coverage_R2I0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H0E: Type2 Hypothesis = Type0 ⊇-Elimination -/
  theorem Coverage_R2H0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E0I: Type2 ⊇-Elimination = Type0 ⊇-Introduction -/
  theorem Coverage_R2E0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I0I: Type2 ⊇-Introduction = Type0 ⊇-Introduction -/
  theorem Coverage_R2I0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H0I: Type2 Hypothesis = Type0 Introduction -/
  theorem Coverage_R2H0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E0H: Type2 ⊇-Elimination = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2E0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I0H: Type2 ⊇-Introduction = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2I0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H0H: Type2 Hypothesis = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R2H0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R20.NODES

namespace COVERAGE.R22.NODES
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E2E: Type2 ⊇-Elimination = Type2 ⊇-Elimination -/
  theorem Coverage_R2E2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I2E: Type2 ⊇-Introduction = Type2 ⊇-Elimination -/
  theorem Coverage_R2I2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H2E: Type2 ⊇-Hypothesis = Type2 ⊇-Elimination -/
  theorem Coverage_R2H2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E2I: Type2 ⊇-Elimination = Type2 ⊇-Introduction -/
  theorem Coverage_R2E2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I2I: Type2 ⊇-Introduction = Type2 ⊇-Introduction -/
  theorem Coverage_R2I2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H2I: Type2 ⊇-Hypothesis = Type2 Introduction -/
  theorem Coverage_R2H2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E2H: Type2 ⊇-Elimination = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2E2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I2H: Type2 ⊇-Introduction = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2I2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H2H: Type2 Hypothesis = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R2H2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R22.NODES

namespace COVERAGE.R10.NODES
  /- R1X0E: Type1 Collapsed Node = Type0 ⊇-Elimination -/
  theorem Coverage_R1X0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type1_collapse (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R1X0I: Type1 Collapsed Node = Type0 ⊇-Introduction -/
  theorem Coverage_R1X0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type1_collapse (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R1X0H: Type1 Collapsed Node = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R1X0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type1_collapse (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R10.NODES

namespace COVERAGE.R12.NODES
  /- R1X2E: Type1 Collapsed Node = Type2 ⊇-Elimination -/
  theorem Coverage_R1X2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type1_collapse (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( T3_Of_T1.Col_Of_Col Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R1X2I: Type1 Collapsed Node = Type2 ⊇-Introduction -/
  theorem Coverage_R1X2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type1_collapse (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( T3_Of_T1.Col_Of_Col Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R1X2H: Type1 Collapsed Node = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R1X2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type1_collapse (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( T3_Of_T1.Col_Of_Col Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R12.NODES

namespace COVERAGE.R30.NODES
  /- R3X0E: Type3 Collapsed Node = Type0 ⊇-Elimination -/
  theorem Coverage_R3X0E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type0_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R3X0I: Type3 Collapsed Node = Type0 ⊇-Introduction -/
  theorem Coverage_R3X0I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type0_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R3X0H: Type3 Collapsed Node = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R3X0H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type0_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R30.NODES

namespace COVERAGE.R32.NODES
  /- R3X2E: Type3 Collapsed Node = Type2 ⊇-Elimination -/
  theorem Coverage_R3X2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R3X2I: Type3 Collapsed Node = Type2 ⊇-Introduction -/
  theorem Coverage_R3X2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R3X2H: Type3 Collapsed Node = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R3X2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R32.NODES


namespace COVERAGE.R22.EDGES
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E2E: Type2 ⊇-Elimination = Type2 ⊇-Elimination -/
  theorem Coverage_R2E2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I2E: Type2 ⊇-Introduction = Type2 ⊇-Elimination -/
  theorem Coverage_R2I2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H2E: Type2 ⊇-Hypothesis = Type2 ⊇-Elimination -/
  theorem Coverage_R2H2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E2I: Type2 ⊇-Elimination = Type2 ⊇-Introduction -/
  theorem Coverage_R2E2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I2I: Type2 ⊇-Introduction = Type2 ⊇-Introduction -/
  theorem Coverage_R2I2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H2I: Type2 ⊇-Hypothesis = Type2 Introduction -/
  theorem Coverage_R2H2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2E2H: Type2 ⊇-Elimination = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2E2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_elimination (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2I2H: Type2 ⊇-Introduction = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2I2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_introduction (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R2H2H: Type2 Hypothesis = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R2H2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type2_hypothesis (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R22.EDGES

namespace COVERAGE.R32.EDGES
  /- R3X2E: Type3 Collapsed Node = Type2 ⊇-Elimination -/
  theorem Coverage_R3X2E {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type2_elimination (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Col_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R3X2I: Type3 Collapsed Node = Type2 ⊇-Introduction -/
  theorem Coverage_R3X2I {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type2_introduction (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Col_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- R3X2H: Type3 Collapsed Node = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R3X2H {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    ( type3_collapse (get_rule U DLDS) ) →
    ( type2_hypothesis (get_rule V DLDS) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Col_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.R32.EDGES

/- End -/
