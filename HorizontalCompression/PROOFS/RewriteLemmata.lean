import HorizontalCompression

set_option linter.unusedSimpArgs false

/- Proofs: Coverage (Same Level) -/

namespace REWRITE
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Method "rewrite_incoming" preserves "≠ []" -/
  theorem NeNil_RwIncoming {COLLAPSE : Vertex} {INCOMING : List Deduction} :
    -----------------------------------------------------------------------------------
    ( collapse.rewrite_incoming COLLAPSE INCOMING ≠ [] → INCOMING ≠ [] ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intros; exact List.cons_ne_nil HEAD TAIL;
  /- Lemma: Method "rewrite_incoming" preserves "List.length" -/
  theorem Eq_Length_RwIncoming {COLLAPSE : Vertex} {INCOMING : List Deduction} :
    -----------------------------------------------------------------------------------
    ( List.length (collapse.rewrite_incoming COLLAPSE INCOMING) = List.length INCOMING ) := by
  match INCOMING with
  | [] => trivial;
  | (HEAD::TAIL) => simp only [collapse.rewrite_incoming];
                    simp only [List.length, Nat.succ.injEq];
                    exact Eq_Length_RwIncoming;
  /- Lemma: Applications of "rewrite_incoming" have fixed "EDGE.END" -/
  theorem Get_End_RwIncoming {COLLAPSE : Vertex} {RWRT : Deduction} {INCOMING : List Deduction} :
    ( RWRT ∈ collapse.rewrite_incoming COLLAPSE INCOMING ) →
    -----------------------------------------------------------------------------------
    ( RWRT.END = COLLAPSE ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_incoming] at mem_cases;
                    cases mem_cases with
                    | head _ => trivial;
                    | tail _ mem_cases => exact Get_End_RwIncoming mem_cases;
  /- Lemma: Predict "rewrite_incoming" membership -/
  theorem Mem_RwIncoming_Of_Mem {COLLAPSE : Vertex} {INC : Deduction} {INCOMING : List Deduction} :
    ( INC ∈ INCOMING ) →
    -----------------------------------------------------------------------------------
    ( edge INC.START COLLAPSE INC.COLOUR INC.DEPENDENCY ∈ collapse.rewrite_incoming COLLAPSE INCOMING ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_incoming];
                    cases mem_cases with
                    | head _ => exact List.Mem.head _;
                    | tail _ mem_cases => apply List.Mem.tail;
                                          exact Mem_RwIncoming_Of_Mem mem_cases;
  /- Lemma: Resolve "rewrite_incoming" mebership -/
  theorem Mem_Of_Mem_RwIncoming {COLLAPSE : Vertex} {RWRT : Deduction} {INCOMING : List Deduction} :
    ( RWRT ∈ collapse.rewrite_incoming COLLAPSE INCOMING ) →
    -----------------------------------------------------------------------------------
    ( ∃(ORIGINAL : Vertex), ( edge RWRT.START ORIGINAL RWRT.COLOUR RWRT.DEPENDENCY ∈ INCOMING ) ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_incoming] at mem_cases;
                    cases mem_cases with
                    | head _ => apply Exists.intro HEAD.END;
                                exact List.Mem.head _;
                    | tail _ mem_cases => have Case_Tail := Mem_Of_Mem_RwIncoming mem_cases;
                                          cases Case_Tail with | intro End_Tail Mem_Tail =>
                                          apply Exists.intro End_Tail;
                                          exact List.Mem.tail HEAD Mem_Tail;

  /- Lemma: Method "rewrite_outgoing" preserves "≠ []" -/
  theorem NeNil_RwOutgoing {COLLAPSE : Vertex} {OUTGOING : List Deduction} :
    -----------------------------------------------------------------------------------
    ( collapse.rewrite_outgoing COLLAPSE OUTGOING ≠ [] → OUTGOING ≠ [] ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intros; exact List.cons_ne_nil HEAD TAIL;
  /- Lemma: Method "rewrite_outgoing" preserves "List.length" -/
  theorem Eq_Length_RwOutgoing {COLLAPSE : Vertex} {OUTGOING : List Deduction} :
    -----------------------------------------------------------------------------------
    ( List.length (collapse.rewrite_outgoing COLLAPSE OUTGOING) = List.length OUTGOING ) := by
  match OUTGOING with
  | [] => trivial;
  | (HEAD::TAIL) => simp only [collapse.rewrite_outgoing];
                    simp only [List.length, Nat.succ.injEq];
                    exact Eq_Length_RwOutgoing;
  /- Lemma: Applications of "rewrite_outgoing" have fixed "EDGE.START" -/
  theorem Get_Start_RwOutgoing {COLLAPSE : Vertex} {RWRT : Deduction} {OUTGOING : List Deduction} :
    ( RWRT ∈ collapse.rewrite_outgoing COLLAPSE OUTGOING ) →
    -----------------------------------------------------------------------------------
    ( RWRT.START = COLLAPSE ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_outgoing] at mem_cases;
                    cases mem_cases with
                    | head _ => trivial;
                    | tail _ mem_cases => exact Get_Start_RwOutgoing mem_cases;
  /- Lemma: Predict "rewrite_outgoing" membership -/
  theorem Mem_RwOutgoing_Of_Mem {COLLAPSE : Vertex} {OUT : Deduction} {OUTGOING : List Deduction} :
    ( OUT ∈ OUTGOING ) →
    -----------------------------------------------------------------------------------
    ( edge COLLAPSE OUT.END OUT.COLOUR OUT.DEPENDENCY ∈ collapse.rewrite_outgoing COLLAPSE OUTGOING ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_outgoing];
                    cases mem_cases with
                    | head _ => exact List.Mem.head _;
                    | tail _ mem_cases => apply List.Mem.tail;
                                          exact Mem_RwOutgoing_Of_Mem mem_cases;
  /- Lemma: Resolve "rewrite_outgoing" mebership -/
  theorem Mem_Of_Mem_RwOutgoing {COLLAPSE : Vertex} {RWRT : Deduction} {OUTGOING : List Deduction} :
    ( RWRT ∈ collapse.rewrite_outgoing COLLAPSE OUTGOING ) →
    -----------------------------------------------------------------------------------
    ( ∃(ORIGINAL : Vertex), ( edge ORIGINAL RWRT.END RWRT.COLOUR RWRT.DEPENDENCY ∈ OUTGOING ) ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_outgoing] at mem_cases;
                    cases mem_cases with
                    | head _ => apply Exists.intro HEAD.START;
                                exact List.Mem.head _;
                    | tail _ mem_cases => have Case_Tail := Mem_Of_Mem_RwOutgoing mem_cases;
                                          cases Case_Tail with | intro Start_Tail Mem_Tail =>
                                          apply Exists.intro Start_Tail;
                                          exact List.Mem.tail HEAD Mem_Tail;

  /- Lemma: Method "rewrite_direct" preserves "≠ []" -/
  theorem NeNil_RwDirect {COLLAPSE : Vertex} {DIRECT : List Ancestral} :
    -----------------------------------------------------------------------------------
    ( collapse.rewrite_direct COLLAPSE DIRECT ≠ [] → DIRECT ≠ [] ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intros; exact List.cons_ne_nil HEAD TAIL;
  /- Lemma: Method "rewrite_direct" preserves "List.length" -/
  theorem Eq_Length_RwDirect {COLLAPSE : Vertex} {DIRECT : List Ancestral} :
    -----------------------------------------------------------------------------------
    ( List.length (collapse.rewrite_direct COLLAPSE DIRECT) = List.length DIRECT ) := by
  match DIRECT with
  | [] => trivial;
  | (HEAD::TAIL) => simp only [collapse.rewrite_direct];
                    simp only [List.length, Nat.succ.injEq];
                    exact Eq_Length_RwDirect;
  /- Lemma: Applications of "rewrite_direct" have fixed "PATH.END" -/
  theorem Get_End_RwDirect {COLLAPSE : Vertex} {RWRT : Ancestral} {DIRECT : List Ancestral} :
    ( RWRT ∈ collapse.rewrite_direct COLLAPSE DIRECT ) →
    -----------------------------------------------------------------------------------
    ( RWRT.END = COLLAPSE ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_direct] at mem_cases;
                    cases mem_cases with
                    | head _ => trivial;
                    | tail _ mem_cases => exact Get_End_RwDirect mem_cases;
  /- Lemma: Predict "rewrite_direct" membership -/
  theorem Mem_RwDirect_Of_Mem {COLLAPSE : Vertex} {DIR : Ancestral} {DIRECT : List Ancestral} :
    ( DIR ∈ DIRECT ) →
    -----------------------------------------------------------------------------------
    ( path DIR.START COLLAPSE DIR.COLOURS ∈ collapse.rewrite_direct COLLAPSE DIRECT ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_direct];
                    cases mem_cases with
                    | head _ => exact List.Mem.head _;
                    | tail _ mem_cases => apply List.Mem.tail;
                                          exact Mem_RwDirect_Of_Mem mem_cases;
  /- Lemma: Resolve "rewrite_direct" mebership -/
  theorem Mem_Of_Mem_RwDirect {COLLAPSE : Vertex} {RWRT : Ancestral} {DIRECT : List Ancestral} :
    ( RWRT ∈ collapse.rewrite_direct COLLAPSE DIRECT ) →
    -----------------------------------------------------------------------------------
    ( ∃(ORIGINAL : Vertex), ( path RWRT.START ORIGINAL RWRT.COLOURS ∈ DIRECT ) ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_direct] at mem_cases;
                    cases mem_cases with
                    | head _ => apply Exists.intro HEAD.END;
                                exact List.Mem.head _;
                    | tail _ mem_cases => have Case_Tail := Mem_Of_Mem_RwDirect mem_cases;
                                          cases Case_Tail with | intro Start_Tail Mem_Tail =>
                                          apply Exists.intro Start_Tail;
                                          exact List.Mem.tail HEAD Mem_Tail;
end REWRITE

/- End -/
