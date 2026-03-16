import HorizontalCompression

set_option linter.unusedSimpArgs false

/- Proofs: Coverage (Same Level) -/

namespace DEFINE
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Define Check Procedure for "ind.COLOURS = [0, RULE.CENTER.NUMBER]" -/
  def check_path_colours (COLOURS : List Nat) (PATHS : List Ancestral) : Prop :=
      match PATHS with
      | [] => True
      | (PATH::PATHS) => ( PATH.COLOURS = COLOURS )
                       ∧ ( check_path_colours COLOURS PATHS )
  theorem Def_Check_Path_Colours {COLOURS : List Nat} {PATH : Ancestral} {PATHS : List Ancestral} :
    ( PATH ∈ PATHS ) →
    ( check_path_colours COLOURS PATHS ) →
    ---------------------------
    ( PATH.COLOURS = COLOURS ) := by
  match PATHS with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases prop_check;
                    simp only [check_path_colours] at prop_check;
                    cases prop_check with | intro prop_check_head prop_check_tail =>
                    cases mem_cases with
                    | head _ => exact prop_check_head;
                    | tail _ mem_cases => exact Def_Check_Path_Colours mem_cases prop_check_tail;

  /- Lemma: Define Check Procedure for "( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START )" -/
  def check_path_starts (PATHS : List Ancestral) : Prop :=
      match PATHS with
      | [] => True
      | (PATH₁::PATHS₂) => ( loop PATH₁ PATHS₂ )
                         ∧ ( check_path_starts PATHS₂ )
    where loop (PATH₁ : Ancestral) (PATHS₂ : List Ancestral) : Prop :=
          match PATHS₂ with
          | [] => True
          | (PATH₂::PATHS₂) => ( PATH₁.COLOURS = PATH₂.COLOURS ↔ PATH₁.START = PATH₂.START )
                             ∧ ( loop PATH₁ PATHS₂ )
  theorem Loop_Check_Path_Starts {PATH₁ PATH₂ : Ancestral} {PATHS₂ : List Ancestral} :
    ( PATH₂ ∈ PATHS₂ ) →
    ( check_path_starts.loop PATH₁ PATHS₂ ) →
    ---------------------------
    ( ( PATH₁.COLOURS = PATH₂.COLOURS ) ↔ ( PATH₁.START = PATH₂.START ) ) := by
  match PATHS₂ with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro case_mem₂ prop_check_loop;
                    simp only [check_path_starts.loop] at prop_check_loop;
                    cases prop_check_loop with | intro prop_check_head prop_check_tail =>
                    cases case_mem₂ with
                    | head _ => exact prop_check_head;
                    | tail _ case_mem₂ => exact Loop_Check_Path_Starts case_mem₂ prop_check_tail;
  theorem Def_Check_Path_Starts {PATH₁ PATH₂ : Ancestral} {PATHS : List Ancestral} :
    ( PATH₁ ∈ PATHS ) →
    ( PATH₂ ∈ PATHS ) →
    ( check_path_starts PATHS ) →
    ---------------------------
    ( ( PATH₁.COLOURS = PATH₂.COLOURS ) ↔ ( PATH₁.START = PATH₂.START ) ) := by
  match PATHS with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro case_mem₁ case_mem₂ prop_check;
                    simp only [check_path_starts] at prop_check;
                    cases prop_check with | intro prop_check_loop prop_check_tail =>
                    cases case_mem₁ with
                    | head _ => cases case_mem₂ with
                                | head _ => simp only [eq_self_iff_true];
                                | tail _ case_mem₂ => exact Loop_Check_Path_Starts case_mem₂ prop_check_loop;
                    | tail _ case_mem₁ => cases case_mem₂ with
                                          | head _ => rewrite [eq_comm];
                                                      rewrite [Loop_Check_Path_Starts case_mem₁ prop_check_loop];
                                                      rewrite [eq_comm];
                                                      trivial;
                                          | tail _ case_mem₂ => exact Def_Check_Path_Starts case_mem₁ case_mem₂ prop_check_tail;

  /- Lemma: Define Check Procedure for "( INC.START = IND.END ) ↔ ( INC = edge IND.END RULE.CENTER 0 dep_inc )" -/
  def check_path_incoming (START END : Vertex) (DEPENDENCY : List Formula) (EDGES : List Deduction) : Prop :=
      match EDGES with
      | [] => True
      | (EDGE::EDGES) => ( EDGE.START = START ↔ EDGE = edge START END 0 DEPENDENCY )
                       ∧ ( check_path_incoming START END DEPENDENCY EDGES )
  theorem Def_Check_Path_Incoming {START END : Vertex} {DEPENDENCY : List Formula} {EDGE : Deduction} {EDGES : List Deduction} :
    ( EDGE ∈ EDGES ) →
    ( check_path_incoming START END DEPENDENCY EDGES ) →
    ---------------------------
    ( EDGE.START = START ↔ EDGE = edge START END 0 DEPENDENCY ) := by
  match EDGES with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases prop_check;
                    simp only [check_path_incoming] at prop_check;
                    cases prop_check with | intro prop_check_head prop_check_tail =>
                    cases mem_cases with
                    | head _ => exact prop_check_head;
                    | tail _ mem_cases => exact Def_Check_Path_Incoming mem_cases prop_check_tail;

  /- Lemma: Define Check Procedure for "( OUT.COLOUR = colour ) ↔ ( OUT = edge RULE.CENTER out colour dep_out )" -/
  def check_path_outgoing (START END : Vertex) (COLOUR : Nat) (DEPENDENCY : List Formula) (EDGES : List Deduction) : Prop :=
      match EDGES with
      | [] => True
      | (EDGE::EDGES) => ( EDGE.COLOUR = COLOUR ↔ EDGE = edge START END COLOUR DEPENDENCY )
                       ∧ ( check_path_outgoing START END COLOUR DEPENDENCY EDGES )
  theorem Def_Check_Path_Outgoing {START END : Vertex} {COLOUR : Nat} {DEPENDENCY : List Formula} {EDGE : Deduction} {EDGES : List Deduction} :
    ( EDGE ∈ EDGES ) →
    ( check_path_outgoing START END COLOUR DEPENDENCY EDGES ) →
    ---------------------------
    ( EDGE.COLOUR = COLOUR ↔ EDGE = edge START END COLOUR DEPENDENCY ) := by
  match EDGES with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases prop_check;
                    simp only [check_path_outgoing] at prop_check;
                    cases prop_check with | intro prop_check_head prop_check_tail =>
                    cases mem_cases with
                    | head _ => exact prop_check_head;
                    | tail _ mem_cases => exact Def_Check_Path_Outgoing mem_cases prop_check_tail;
end DEFINE

/- End -/
