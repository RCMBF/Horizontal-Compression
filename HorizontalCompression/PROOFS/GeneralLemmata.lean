import HorizontalCompression

set_option linter.unusedSimpArgs false

/- General Proofs: -/

namespace List
  /- List.Mem (∈) -/
  theorem Elem_Eq_True_Iff_Mem [DecidableEq α] {a : α} {as : List α} :
    ( a ∈ as ) ↔ ( elem a as = true ) := by
  exact Iff.intro List.elem_eq_true_of_mem List.mem_of_elem_eq_true;
  --
  theorem False_Iff_Mem_Nil [DecidableEq α] {a : α} :
    ( a ∈ [] ) ↔ ( False ) := by
  exact Iff.intro ( by intros; trivial; ) ( by intros; trivial; );
  --
  theorem Eq_Iff_Mem_Unit [DecidableEq α] {a₁ a₂ : α} :
    ( a₁ ∈ [a₂] ) ↔ ( a₁ = a₂ ) := by
  exact Iff.intro ( by intro mem_cases;
                       cases mem_cases with
                       | head _ => rfl;
                       | tail _ _ => trivial; )
                  ( by intro case_eq;
                       rewrite [case_eq];
                       exact List.Mem.head []; )
  --
  theorem Eq_Or_Mem_Iff_Mem_Cons [DecidableEq α] {a₁ a₂ : α} {as₂ : List α} :
    ( a₁ ∈ a₂::as₂ ) ↔ ( a₁ = a₂ ) ∨ ( a₁ ∈ as₂ ) := by
  exact Iff.intro ( by intro case_cons;
                       cases case_cons with
                       | head _ => exact Or.inl rfl;
                       | tail _ mem_cases => exact Or.inr mem_cases; )
                  ( by intro case_or;
                       cases case_or with
                       | inl case_eq => rewrite [case_eq];
                                        exact List.Mem.head as₂;
                       | inr mem_cases => exact List.Mem.tail a₂ mem_cases; )

  /- List.append (++) -/
  theorem NeNil_Or_NeNil_Of_NeNil_Append [DecidableEq α] {as₁ as₂ : List α} :
    ( as₁ ++ as₂ ≠ [] ) → ( as₁ ≠ [] ) ∨ ( as₂ ≠ [] ) := by
  match as₁ with
  | [] => intro case_append;
          rewrite [List.nil_append] at case_append;
          exact Or.inr case_append;
  | (HEAD::TAIL) => intros; exact Or.inl (List.cons_ne_nil HEAD TAIL);
  --
  theorem Mem_Or_Mem_Of_Mem_Append [DecidableEq α] {a : α} {as₁ as₂ : List α} :
    ( a ∈ as₁ ++ as₂ ) → ( a ∈ as₁ ) ∨ ( a ∈ as₂ ) := by
  match as₁ with
  | [] => intro case_append;
          rewrite [List.nil_append] at case_append;
          exact Or.inr case_append;
  | (HEAD::TAIL) => intro case_append;
                    cases case_append with
                    | head _ => exact Or.inl (List.Mem.head TAIL);
                    | tail _ case_append => cases Mem_Or_Mem_Of_Mem_Append case_append with
                                            | inl mem_tail => exact Or.inl (List.Mem.tail HEAD mem_tail);
                                            | inr mem_as₂ => exact Or.inr mem_as₂;
  theorem Mem_Append_Of_Mem_Or_Mem [DecidableEq α] {a : α} {as₁ as₂ : List α} :
    ( a ∈ as₁ ) ∨ ( a ∈ as₂ ) → ( a ∈ as₁ ++ as₂ ) := by
  intro case_or;
  cases case_or with
  | inl mem_as₁ => exact List.mem_append_left as₂ mem_as₁;
  | inr mem_as₂ => exact List.mem_append_right as₁ mem_as₂;
  theorem Mem_Or_Mem_Iff_Mem_Append [DecidableEq α] {a : α} {as₁ as₂ : List α} :
    ( a ∈ as₁ ++ as₂ ) ↔ ( a ∈ as₁ ) ∨ ( a ∈ as₂ ) := by
  exact Iff.intro Mem_Or_Mem_Of_Mem_Append Mem_Append_Of_Mem_Or_Mem;

  /- List.removeAll (--) -/
  theorem RemoveAll_Nil [DecidableEq α] {bs : List α} :
    ( List.removeAll [] bs = [] ) := by
  simp only [List.removeAll];
  trivial;
  theorem RemoveAll_Cons [DecidableEq α] {a : α} {as bs : List α} :
    ( List.removeAll (a::as) bs = if   ( a ∈ bs )
                                  then ( List.removeAll as bs )
                                  else ( a::List.removeAll as bs ) ) := by
  match as with
  | [] => simp only [Elem_Eq_True_Iff_Mem];
          simp only [List.removeAll];
          simp only [List.filter];
          split;
          case _ case_false => simp only [Bool.not_eq_true'] at case_false;
                               simp only [case_false];
                               simp only [Bool.false_eq_true];
                               simp only [ite_false];
          case _ case_true => simp only [Bool.not_eq_false'] at case_true;
                              simp only [case_true];
                              simp only [ite_true];
  | (HEAD::TAIL) => simp only [Elem_Eq_True_Iff_Mem];
                    simp only [List.removeAll];
                    simp only [List.filter];
                    split;
                    case _ case_false => simp only [Bool.not_eq_true'] at case_false;
                                         simp only [case_false];
                                         simp only [Bool.false_eq_true];
                                         simp only [ite_false];
                    case _ case_true => simp only [Bool.not_eq_false'] at case_true;
                                        simp only [case_true];
                                        simp only [ite_true];
  theorem Mem_Of_Mem_RemoveAll [DecidableEq α] {a : α} {as bs : List α} :
    ( a ∈ List.removeAll as bs ) → ( a ∈ as ) := by
  match as with
  | [] => intro mem_remove;
          rewrite [RemoveAll_Nil] at mem_remove;
          trivial;
  | (HEAD::TAIL) => intro mem_remove;
                    rewrite [RemoveAll_Cons] at mem_remove;
                    split at mem_remove;
                    case _ _ => apply List.Mem.tail HEAD;
                                exact (Mem_Of_Mem_RemoveAll mem_remove);
                    case _ _ => cases mem_remove with
                                | head _ => exact List.Mem.head TAIL;
                                | tail _ mem_remove => apply List.Mem.tail HEAD;
                                                       exact (Mem_Of_Mem_RemoveAll mem_remove);
end List

namespace COLLAPSE
  /- Lemma: Simplify "check_numbers [UNIT]" -/
  theorem Check_Numbers_Unit {UNIT : Nat} :
    ( UNIT > 0 ) →
    ---------------------------
    ( check_numbers [UNIT] ) := by
  intro prop_unit;
  simp only [check_numbers];
  exact And.intro ( by rewrite [ne_eq];
                       simp only [List.cons_ne_self];
                       exact not_false; )
                  ( by intro colour mem_cases;
                       cases mem_cases with
                       | head _ => exact prop_unit;
                       | tail _ mem_cases => trivial; );
  /- Lemma: Simplify "check_numbers (HEAD::TAIL)" -/
  theorem Check_Numbers_Cons {HEAD : Nat} {TAIL : List Nat} :
    ( HEAD > 0 ) →
    ( check_numbers TAIL ) →
    ---------------------------
    ( check_numbers (HEAD::TAIL) ) := by
  intro prop_head prop_tail;
  simp only [check_numbers] at prop_tail ⊢;
  cases prop_tail with | intro prop_nil prop_mem =>
  exact And.intro ( by exact List.cons_ne_nil HEAD TAIL; )
                  ( by intro colour mem_cases;
                       cases mem_cases with
                       | head _ => exact prop_head;
                       | tail _ mem_cases => exact prop_mem mem_cases; );

  /- Lemma: Simplify "END" at "get_rule.incoming" -/
  theorem Simp_End_Incoming {NODE : Vertex} {DLDS : Graph} {EDGE : Deduction} :
    ( EDGE ∈ get_rule.incoming NODE DLDS ) →
    ------------------------------------
    ( EDGE.END = NODE ) := by
  simp only [get_rule.incoming];
  induction DLDS.EDGES with
  | nil => intro mem_incoming;
           simp only [get_rule.incoming.loop] at mem_incoming;
           trivial;
  | cons HEAD TAIL LOOP => intro mem_incoming;
                           simp only [get_rule.incoming.loop] at mem_incoming;
                           split at mem_incoming;
                           case _ eq_head => cases mem_incoming with
                                             | head _ => exact eq_head;
                                             | tail _ mem_incoming => exact LOOP mem_incoming;
                           case _ ne_head => exact LOOP mem_incoming;
  /- Lemma: Simplify "START" at "get_rule.outgoing" -/
  theorem Simp_Start_Outgoing {NODE : Vertex} {DLDS : Graph} {EDGE : Deduction} :
    ( EDGE ∈ get_rule.outgoing NODE DLDS ) →
    ------------------------------------
    ( EDGE.START = NODE ) := by
  simp only [get_rule.outgoing];
  induction DLDS.EDGES with
  | nil => intro mem_incoming;
           simp only [get_rule.outgoing.loop] at mem_incoming;
           trivial;
  | cons HEAD TAIL LOOP => intro mem_incoming;
                           simp only [get_rule.outgoing.loop] at mem_incoming;
                           split at mem_incoming;
                           case _ eq_head => cases mem_incoming with
                                             | head _ => exact eq_head;
                                             | tail _ mem_incoming => exact LOOP mem_incoming;
                           case _ ne_head => exact LOOP mem_incoming;
  /- Lemma: Simplify "END" at "get_rule.direct" -/
  theorem Simp_End_Direct {NODE : Vertex} {DLDS : Graph} {PATH : Ancestral} :
    ( PATH ∈ get_rule.direct NODE DLDS ) →
    ------------------------------------
    ( PATH.END = NODE ) := by
  simp only [get_rule.direct];
  induction DLDS.PATHS with
  | nil => intro mem_direct;
           simp only [get_rule.direct.loop] at mem_direct;
           trivial;
  | cons HEAD TAIL LOOP => intro mem_direct;
                           simp only [get_rule.direct.loop] at mem_direct;
                           split at mem_direct;
                           case _ eq_head => cases mem_direct with
                                             | head _ => exact eq_head;
                                             | tail _ mem_direct => exact LOOP mem_direct;
                           case _ ne_head => exact LOOP mem_direct;

  /- Lemma: Simplify "get_rule.direct" at "get_rule.indirect" -/
  theorem Simp_Direct_Indirect₁₃ {NODE₀ NODE₁ : Vertex} {DLDS : Graph} :
    ( path (Start : Vertex) NODE₁ (Colours : List Nat) ∈ get_rule.indirect NODE₀ DLDS ) →
    ------------------------------------
    ( path (Start : Vertex) NODE₁ (Colours : List Nat) ∈ get_rule.direct NODE₁ DLDS ) := by
  simp only [get_rule.indirect];
  induction get_rule.incoming NODE₀ DLDS with
  | nil => intro prop_indirect₀;
           simp only [get_rule.indirect.loop] at prop_indirect₀;
           trivial;
  | cons HEAD TAIL LOOP => intro prop_indirect₀;
                           simp only [get_rule.indirect.loop] at prop_indirect₀;
                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at prop_indirect₀;
                           cases prop_indirect₀ with
                           | inl prop_head₀ => rewrite [←get_rule.direct] at prop_head₀;    /- Revert; Fold at "prop_head₀" -/
                                               rewrite [←COLLAPSE.Simp_End_Direct prop_head₀] at prop_head₀;
                                               exact prop_head₀;
                           | inr prop_tail₀ => exact LOOP prop_tail₀;
  /- Lemma: Simplify "get_rule.direct" at "get_rule.indirect" -/
  theorem Simp_Direct_Indirect₀₂ {NODE : Vertex} {DLDS : Graph} {EDGE : Deduction} :
    ( EDGE ∈ get_rule.incoming NODE DLDS ) →
    ( get_rule.indirect NODE DLDS = [] ) →
    ------------------------------------
    ( get_rule.direct EDGE.START DLDS = [] ) := by
  simp only [get_rule.indirect];
  induction get_rule.incoming NODE DLDS with
  | nil => intro _ prop_indirect;
           simp only [get_rule.indirect.loop] at prop_indirect;
           trivial;
  | cons HEAD TAIL LOOP => intro prop_incoming prop_indirect;
                           simp only [get_rule.indirect.loop] at prop_indirect;
                           simp only [List.append_eq_nil_iff] at prop_indirect;
                           cases prop_indirect with | intro prop_indirect_head prop_indirect_tail =>
                           simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at prop_incoming;
                           cases prop_incoming with
                           | inl prop_incoming_head => rewrite [←get_rule.direct] at prop_indirect_head;    /- Revert; Fold at "prop_indirect_head" -/
                                                       rewrite [←prop_incoming_head] at prop_indirect_head;
                                                       exact prop_indirect_head;
                           | inr prop_incoming_tail => exact LOOP prop_incoming_tail prop_indirect_tail;

  /- Lemma: Simplify "END" at "type_incoming" -/
  theorem Simp_Inc_End {INC : Deduction} {CENTER : Vertex} {INDIRECT : List Ancestral} :
    ( type_incoming.check INC CENTER INDIRECT ) →
    ---------------------------------------------------------------------------------
    ( INC.END = CENTER ) := by
  intro inc_case;
  simp only [type_incoming.check] at inc_case;
  cases inc_case with | intro prop_start inc_case =>
  cases inc_case with | intro prop_end prop_colour =>
  exact prop_end;
  /- Lemma: Simplify "START" at "type_outgoing₁" -/
  theorem Simp_Out_Start₁ {OUT : Deduction} {CENTER : Vertex} {INDIRECT : List Ancestral} :
    ( ( type_outgoing₁.check_h₁ OUT CENTER ) ∨ ( type_outgoing₁.check_ie₁ OUT CENTER INDIRECT ) ) →
    ---------------------------------------------------------------------------------
    ( OUT.START = CENTER ) := by
  intro out_cases;
  cases out_cases with
  | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                       cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                       cases out_caseₕ₁ with | intro prop_startₕ₁ out_caseₕ₁ =>
                       exact prop_startₕ₁;
  | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                        cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_startᵢₑ₁ out_caseᵢₑ₁ =>
                        exact prop_startᵢₑ₁;
  /- Lemma: Simplify "START" at "type_outgoing₃" -/
  theorem Simp_Out_Start₃ {OUT : Deduction} {CENTER : Vertex} {DIRECT INDIRECT : List Ancestral} :
    ( ( ( type_outgoing₁.check_h₁ OUT CENTER ) ∨ ( type_outgoing₁.check_ie₁ OUT CENTER INDIRECT ) )
    ∨ ( ( type_outgoing₃.check_h₃ OUT CENTER DIRECT ) ∨ ( type_outgoing₃.check_ie₃ OUT CENTER INDIRECT ) ) ) →
    ---------------------------------------------------------------------------------
    ( OUT.START = CENTER ) := by
  intro out_cases;
  cases out_cases with
  | inl out_case₁ => cases out_case₁ with
                      | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                                           cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                                           cases out_caseₕ₁ with | intro prop_startₕ₁ out_caseₕ₁ =>
                                           exact prop_startₕ₁;
                      | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                                            cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_startᵢₑ₁ out_caseᵢₑ₁ =>
                                            exact prop_startᵢₑ₁;
  | inr out_case₃ => cases out_case₃ with
                      | inl out_caseₕ₃ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₃;
                                           cases out_caseₕ₃ with | intro prop_hptₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_startₕ₃ out_caseₕ₃ =>
                                           exact prop_startₕ₃;
                      | inr out_caseᵢₑ₃ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₃;
                                            cases out_caseᵢₑ₃ with | intro prop_hptᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_startᵢₑ₃ out_caseᵢₑ₃ =>
                                            exact prop_startᵢₑ₃;
  /- Lemma: Simplify "COLOUR" at "type_outgoing₁" -/
  theorem Simp_Out_Colour₁ {OUT : Deduction} {CENTER : Vertex} {INDIRECT : List Ancestral} :
    ( ( type_outgoing₁.check_h₁ OUT CENTER ) ∨ ( type_outgoing₁.check_ie₁ OUT CENTER INDIRECT ) ) →
    ---------------------------------------------------------------------------------
    ( ( OUT.COLOUR = 0 )
    ∨ ( OUT.COLOUR ∈ (CENTER.NUMBER::CENTER.PAST) ) ) := by
  intro out_cases;
  cases out_cases with
  | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                       cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                       cases out_caseₕ₁ with | intro prop_startₕ₁ out_caseₕ₁ =>
                       cases out_caseₕ₁ with | intro prop_endₕ₁ prop_colourₕ₁ =>
                       exact Or.inl prop_colourₕ₁;
  | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                        cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_startᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_endᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_colourᵢₑ₁ prop_out_indᵢₑ₁ =>
                        exact Or.inr prop_colourᵢₑ₁;
  /- Lemma: Simplify "COLOUR" at "type_outgoing₃" -/
  theorem Simp_Out_Colour₃ {OUT : Deduction} {CENTER : Vertex} {DIRECT INDIRECT : List Ancestral} :
    ( ( ( type_outgoing₁.check_h₁ OUT CENTER ) ∨ ( type_outgoing₁.check_ie₁ OUT CENTER INDIRECT ) )
    ∨ ( ( type_outgoing₃.check_h₃ OUT CENTER DIRECT ) ∨ ( type_outgoing₃.check_ie₃ OUT CENTER INDIRECT ) ) ) →
    ---------------------------------------------------------------------------------
    ( ( OUT.COLOUR = 0 )
    ∨ ( OUT.COLOUR ∈ (CENTER.NUMBER::CENTER.PAST) ) ) := by
  intro out_cases;
  cases out_cases with
  | inl out_case₁ => cases out_case₁ with
                      | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                                           cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                                           cases out_caseₕ₁ with | intro prop_startₕ₁ out_caseₕ₁ =>
                                           cases out_caseₕ₁ with | intro prop_endₕ₁ prop_colourₕ₁ =>
                                           exact Or.inl prop_colourₕ₁;
                      | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                                            cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_startᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_endᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_colourᵢₑ₁ prop_out_indᵢₑ₁ =>
                                            exact Or.inr prop_colourᵢₑ₁;
  | inr out_case₃ => cases out_case₃ with
                      | inl out_caseₕ₃ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₃;
                                           cases out_caseₕ₃ with | intro prop_hptₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_startₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_endₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_colourₕ₃ prop_out_dirₕ₃ =>
                                           exact Or.inr prop_colourₕ₃;
                      | inr out_caseᵢₑ₃ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₃;
                                            cases out_caseᵢₑ₃ with | intro prop_hptᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_startᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_endᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_colourᵢₑ₃ prop_out_indᵢₑ₃ =>
                                            exact Or.inr prop_colourᵢₑ₃;

  /- Lemma: Simplify "U.COLLAPSED = true" at "Graph.is_collapse" -/
  theorem Simp_Rule_Above_Collapse {U V : Vertex} {DLDS CLPS : Graph} :
    ( U.COLLAPSED = true ) →
    ( CLPS.is_collapse U V DLDS ) →
    /- Incoming Nodes -/-------------------------------------------------------------
    ( ∀{inc : Deduction}, ( inc ∈ get_rule.incoming U DLDS ) →
      -----------------------------------------------------------------------------
    ( get_rule inc.START CLPS = rule ( inc.START )
                                     ( get_rule.incoming inc.START DLDS )
  /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (get_rule.outgoing inc.START DLDS) )
  /- Direct Inc ∈ Indirect UV -/     ( get_rule.direct inc.START DLDS )
                                     ( get_rule.indirect inc.START DLDS ) ) ) := by
  intro prop_col prop_collapse;
  simp only [Graph.is_collapse] at prop_collapse;
  cases prop_collapse with | intro prop_incoming _ =>
  intro edge prop_mem;
  exact prop_incoming prop_col prop_mem;
  /- Lemma: Simplify "U.COLLAPSED = false" at "Graph.is_collapse" -/
  theorem Simp_Rule_Above_Left {U V : Vertex} {DLDS CLPS : Graph} :
    ( U.COLLAPSED = false ) →
    ( CLPS.is_collapse U V DLDS ) →
    /- Incoming Nodes -/-------------------------------------------------------------
    ( ∀{inc : Deduction}, ( inc ∈ get_rule.incoming U DLDS ) →
      -----------------------------------------------------------------------------
      ( get_rule inc.START CLPS = rule ( inc.START )
                                       ( get_rule.incoming inc.START DLDS )
    /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (get_rule.outgoing inc.START DLDS) )
    /- Direct Inc ∈ Indirect UV -/     ( get_rule.direct.loop ( inc.START )
                                                              ( pre_collapse.indirect ( U.NUMBER )
                                                                                      ( U.HYPOTHESIS )
                                                                                      ( get_rule.incoming U DLDS )
                                                                                      ( get_rule.outgoing U DLDS )
                                                                                      ( get_rule.direct U DLDS ) ) )
                                       ( get_rule.indirect inc.START DLDS ) ) ) := by
  intro prop_col prop_collapse;
  simp only [Graph.is_collapse] at prop_collapse;
  cases prop_collapse with | intro _ prop_collapse =>
  cases prop_collapse with | intro prop_incoming _ =>
  intro edge prop_mem;
  exact prop_incoming prop_col prop_mem;
  /- Lemma: Simplify "V" at "Graph.is_collapse" -/
  theorem Simp_Rule_Above_Right {U V : Vertex} {DLDS CLPS : Graph} :
    ( CLPS.is_collapse U V DLDS ) →
    /- Incoming Nodes -/-------------------------------------------------------------
    ( ∀{inc : Deduction}, ( inc ∈ get_rule.incoming V DLDS ) →
      -----------------------------------------------------------------------------
      ( get_rule inc.START CLPS = rule ( inc.START )
                                       ( get_rule.incoming inc.START DLDS )
    /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end V (collapse.center U V) (get_rule.outgoing inc.START DLDS) )
    /- Direct Inc ∈ Indirect UV -/     ( get_rule.direct.loop ( inc.START )
                                                              ( pre_collapse.indirect ( V.NUMBER )
                                                                                      ( V.HYPOTHESIS )
                                                                                      ( get_rule.incoming V DLDS )
                                                                                      ( get_rule.outgoing V DLDS )
                                                                                      ( get_rule.direct V DLDS ) ) )
                                       ( get_rule.indirect inc.START DLDS ) ) ) := by
  intro prop_collapse;
  simp only [Graph.is_collapse] at prop_collapse;
  cases prop_collapse with | intro _ prop_collapse =>
  cases prop_collapse with | intro _ prop_incoming =>
  intro edge prop_mem;
  exact prop_incoming prop_mem;
end COLLAPSE

/- End -/
