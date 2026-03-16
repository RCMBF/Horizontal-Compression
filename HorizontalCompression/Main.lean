import HorizontalCompression
import PROOFS.SameLevelCoverage
import PROOFS.UpperLevelCoverage

set_option linter.unusedSimpArgs false

/- Theorem: Coverage Theorem (Collapse Nodes) -/
namespace COVERAGE.MAIN.NODES
  --333 set_option trace.Meta.Tactic.simp true
  /- Coverage Theorem: Type1 of Type0 & Type0 -/
  theorem T1CoverageT0T0 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type0_elimination (get_rule U DLDS) )
    ∨ ( type0_introduction (get_rule U DLDS) )
    ∨ ( type0_hypothesis (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (get_rule V DLDS) )
    ∨ ( type0_introduction (get_rule V DLDS) )
    ∨ ( type0_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type0Eᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R00.NODES.Coverage_R0E0E prop_check_nodes prop_type0Eᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R00.NODES.Coverage_R0E0I prop_check_nodes prop_type0Eᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R00.NODES.Coverage_R0E0H prop_check_nodes prop_type0Eᵤ prop_type0Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type0Iᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R00.NODES.Coverage_R0I0E prop_check_nodes prop_type0Iᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R00.NODES.Coverage_R0I0I prop_check_nodes prop_type0Iᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R00.NODES.Coverage_R0I0H prop_check_nodes prop_type0Iᵤ prop_type0Hᵥ;
                        | inr prop_type0Hᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R00.NODES.Coverage_R0H0E prop_check_nodes prop_type0Hᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R00.NODES.Coverage_R0H0I prop_check_nodes prop_type0Hᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R00.NODES.Coverage_R0H0H prop_check_nodes prop_type0Hᵤ prop_type0Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Coverage Theorem: Type1 of Type1 & Type0 -/
  theorem T1CoverageT1T0 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type1_collapse (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (get_rule V DLDS) )
    ∨ ( type0_introduction (get_rule V DLDS) )
    ∨ ( type0_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type1_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_type1Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R10.NODES.Coverage_R1X0E prop_check_nodes prop_type1Xᵤ prop_type0Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R10.NODES.Coverage_R1X0I prop_check_nodes prop_type1Xᵤ prop_type0Iᵥ;
                        | inr prop_type0Hᵥ => exact R10.NODES.Coverage_R1X0H prop_check_nodes prop_type1Xᵤ prop_type0Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Coverage Theorem: Type3 of Type0 & Type2 -/
  theorem T3CoverageT0T2 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type0_elimination (get_rule U DLDS) )
    ∨ ( type0_introduction (get_rule U DLDS) )
    ∨ ( type0_hypothesis (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (get_rule V DLDS) )
    ∨ ( type2_introduction (get_rule V DLDS) )
    ∨ ( type2_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type0Eᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R02.NODES.Coverage_R0E2E prop_check_nodes prop_type0Eᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R02.NODES.Coverage_R0E2I prop_check_nodes prop_type0Eᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R02.NODES.Coverage_R0E2H prop_check_nodes prop_type0Eᵤ prop_type2Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type0Iᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R02.NODES.Coverage_R0I2E prop_check_nodes prop_type0Iᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R02.NODES.Coverage_R0I2I prop_check_nodes prop_type0Iᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R02.NODES.Coverage_R0I2H prop_check_nodes prop_type0Iᵤ prop_type2Hᵥ;
                        | inr prop_type0Hᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R02.NODES.Coverage_R0H2E prop_check_nodes prop_type0Hᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R02.NODES.Coverage_R0H2I prop_check_nodes prop_type0Hᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R02.NODES.Coverage_R0H2H prop_check_nodes prop_type0Hᵤ prop_type2Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- Coverage Theorem: Type3 of Type2 & Type0 -/
  theorem T3CoverageT2T0 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type2_elimination (get_rule U DLDS) )
    ∨ ( type2_introduction (get_rule U DLDS) )
    ∨ ( type2_hypothesis (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (get_rule V DLDS) )
    ∨ ( type0_introduction (get_rule V DLDS) )
    ∨ ( type0_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type2Eᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R20.NODES.Coverage_R2E0E prop_check_nodes prop_type2Eᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R20.NODES.Coverage_R2E0I prop_check_nodes prop_type2Eᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R20.NODES.Coverage_R2E0H prop_check_nodes prop_type2Eᵤ prop_type0Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type2Iᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R20.NODES.Coverage_R2I0E prop_check_nodes prop_type2Iᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R20.NODES.Coverage_R2I0I prop_check_nodes prop_type2Iᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R20.NODES.Coverage_R2I0H prop_check_nodes prop_type2Iᵤ prop_type0Hᵥ;
                        | inr prop_type2Hᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R20.NODES.Coverage_R2H0E prop_check_nodes prop_type2Hᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R20.NODES.Coverage_R2H0I prop_check_nodes prop_type2Hᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R20.NODES.Coverage_R2H0H prop_check_nodes prop_type2Hᵤ prop_type0Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- Coverage Theorem: Type3 of Type2 & Type2 -/
  theorem T3CoverageT2T2 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type2_elimination (get_rule U DLDS) )
    ∨ ( type2_introduction (get_rule U DLDS) )
    ∨ ( type2_hypothesis (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (get_rule V DLDS) )
    ∨ ( type2_introduction (get_rule V DLDS) )
    ∨ ( type2_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type2Eᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.NODES.Coverage_R2E2E prop_check_nodes prop_type2Eᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.NODES.Coverage_R2E2I prop_check_nodes prop_type2Eᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.NODES.Coverage_R2E2H prop_check_nodes prop_type2Eᵤ prop_type2Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type2Iᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.NODES.Coverage_R2I2E prop_check_nodes prop_type2Iᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.NODES.Coverage_R2I2I prop_check_nodes prop_type2Iᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.NODES.Coverage_R2I2H prop_check_nodes prop_type2Iᵤ prop_type2Hᵥ;
                        | inr prop_type2Hᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.NODES.Coverage_R2H2E prop_check_nodes prop_type2Hᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.NODES.Coverage_R2H2I prop_check_nodes prop_type2Hᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.NODES.Coverage_R2H2H prop_check_nodes prop_type2Hᵤ prop_type2Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Coverage Theorem: Type3 of Type1 & Type2 -/
  theorem T3CoverageT1T2 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type1_collapse (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (get_rule V DLDS) )
    ∨ ( type2_introduction (get_rule V DLDS) )
    ∨ ( type2_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_type1Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R12.NODES.Coverage_R1X2E prop_check_nodes prop_type1Xᵤ prop_type2Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R12.NODES.Coverage_R1X2I prop_check_nodes prop_type1Xᵤ prop_type2Iᵥ;
                        | inr prop_type2Hᵥ => exact R12.NODES.Coverage_R1X2H prop_check_nodes prop_type1Xᵤ prop_type2Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- Coverage Theorem: Type3 of Type3 & Type0 -/
  theorem T3CoverageT3T0 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type3_collapse (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (get_rule V DLDS) )
    ∨ ( type0_introduction (get_rule V DLDS) )
    ∨ ( type0_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_type3Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R30.NODES.Coverage_R3X0E prop_check_nodes prop_type3Xᵤ prop_type0Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R30.NODES.Coverage_R3X0I prop_check_nodes prop_type3Xᵤ prop_type0Iᵥ;
                        | inr prop_type0Hᵥ => exact R30.NODES.Coverage_R3X0H prop_check_nodes prop_type3Xᵤ prop_type0Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------
  /- Coverage Theorem: Type3 of Type3 & Type2 -/
  theorem T3CoverageT3T2 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_nodes (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type3_collapse (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (get_rule V DLDS) )
    ∨ ( type2_introduction (get_rule V DLDS) )
    ∨ ( type2_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_nodes prop_type3Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R32.NODES.Coverage_R3X2E prop_check_nodes prop_type3Xᵤ prop_type2Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R32.NODES.Coverage_R3X2I prop_check_nodes prop_type3Xᵤ prop_type2Iᵥ;
                        | inr prop_type2Hᵥ => exact R32.NODES.Coverage_R3X2H prop_check_nodes prop_type3Xᵤ prop_type2Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.MAIN.NODES


/- Theorem: Coverage Theorem (Collapse Nodes & Edges) -/
namespace COVERAGE.MAIN.EDGES
  --333 set_option trace.Meta.Tactic.simp true
  /- Coverage Theorem: Type3 of Type2 & Type2 -/
  theorem T3CoverageT2T2 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type2_elimination (get_rule U DLDS) )
    ∨ ( type2_introduction (get_rule U DLDS) )
    ∨ ( type2_hypothesis (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (get_rule V DLDS) )
    ∨ ( type2_introduction (get_rule V DLDS) )
    ∨ ( type2_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type2Eᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.EDGES.Coverage_R2E2E prop_check_edges prop_type2Eᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.EDGES.Coverage_R2E2I prop_check_edges prop_type2Eᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.EDGES.Coverage_R2E2H prop_check_edges prop_type2Eᵤ prop_type2Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type2Iᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.EDGES.Coverage_R2I2E prop_check_edges prop_type2Iᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.EDGES.Coverage_R2I2I prop_check_edges prop_type2Iᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.EDGES.Coverage_R2I2H prop_check_edges prop_type2Iᵤ prop_type2Hᵥ;
                        | inr prop_type2Hᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.EDGES.Coverage_R2H2E prop_check_edges prop_type2Hᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.EDGES.Coverage_R2H2I prop_check_edges prop_type2Hᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.EDGES.Coverage_R2H2H prop_check_edges prop_type2Hᵤ prop_type2Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------

  /- Coverage Theorem: Type3 of Type3 & Type2 -/
  theorem T3CoverageT3T2 {U V : Vertex} {DLDS : Graph} :
    ( check_collapse_edges (pre_collapse (get_rule U DLDS) )
                           (pre_collapse (get_rule V DLDS) ) ) →
    /- Left-Side Node (U) -/
    ( ( type3_collapse (get_rule U DLDS) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (get_rule V DLDS) )
    ∨ ( type2_introduction (get_rule V DLDS) )
    ∨ ( type2_hypothesis (get_rule V DLDS) ) ) →
    ---------------------------
    ( type3_collapse (collapse_rule U V DLDS) ) := by
  intro prop_check_edges prop_type3Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R32.EDGES.Coverage_R3X2E prop_check_edges prop_type3Xᵤ prop_type2Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R32.EDGES.Coverage_R3X2I prop_check_edges prop_type3Xᵤ prop_type2Iᵥ;
                        | inr prop_type2Hᵥ => exact R32.EDGES.Coverage_R3X2H prop_check_edges prop_type3Xᵤ prop_type2Hᵥ;
  -----------------------------------------------------------------------------------------------------------------------------------------
end COVERAGE.MAIN.EDGES

/- End -/
