import Init
import BASICS.MyList
import BASICS.MyTypes

/- Neighborhood Type Hierarchy -/
/- Neighborhood: Type 0 (Non-Collapsed Node Without Incoming Ancestral Paths) ⊇-Elimination -/
def type0_elimination (RULE : Neighborhood) : Prop :=
    ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 ) ∧ ( RULE.CENTER.HYPOTHESIS = false )
  ∧ ( RULE.CENTER.COLLAPSED = false ) ∧ ( RULE.CENTER.PAST = [] )
  ∧ ( ∃(inc_nbr out_nbr : Nat),
      ∃(antecedent out_fml : Formula),
      ∃(major_hpt minor_hpt : Bool),
      ∃(major_dep minor_dep : List Formula),
      ------------------------------------------------------
      ( inc_nbr > 0 ) ∧ ( out_nbr > 0 )
    ∧ RULE.INCOMING = [ edge (node (inc_nbr+1)
                                   (RULE.CENTER.LEVEL+1)
                                   (antecedent>>RULE.CENTER.FORMULA)
                                   (major_hpt)
                                   (false)
                                   []) /- Left Child & Major Premise -/
                             RULE.CENTER
                             0
                             #major_dep,
                        edge (node inc_nbr (RULE.CENTER.LEVEL+1) antecedent minor_hpt false []) /- Right Child & Minor Premise -/
                             RULE.CENTER
                             0
                             #minor_dep ]
    ∧ RULE.OUTGOING = [ edge RULE.CENTER
                             (node out_nbr (RULE.CENTER.LEVEL-1) out_fml false false [])
                             0
                             (minor_dep ∪ major_dep) ]
    ∧ RULE.DIRECT   = []
    ∧ RULE.INDIRECT = [] )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Neighborhood: Type 0 (Non-Collapsed Node Without Incoming Ancestral Paths) ⊇-Introduction -/
def type0_introduction (RULE : Neighborhood) : Prop :=
    ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 ) ∧ ( RULE.CENTER.HYPOTHESIS = false )
  ∧ ( RULE.CENTER.COLLAPSED = false ) ∧ ( RULE.CENTER.PAST = [] )
  ∧ ( ∃(inc_nbr out_nbr : Nat),
      ∃(antecedent consequent out_fml : Formula),
      ∃(inc_dep : List Formula),
    ------------------------------------------------------
      ( RULE.CENTER.FORMULA = antecedent>>consequent )
    ∧ ( inc_nbr > 0 ) ∧ ( out_nbr > 0 )
    ∧ RULE.INCOMING = [ edge (node inc_nbr (RULE.CENTER.LEVEL+1) consequent false false [])  /- Unique Child & Sole Premise -/
                             RULE.CENTER
                             0
                             #inc_dep ]
    ∧ RULE.OUTGOING = [ edge RULE.CENTER
                             (node out_nbr (RULE.CENTER.LEVEL-1) out_fml false false [])
                             0
                             (inc_dep − [antecedent]) ]
    ∧ RULE.DIRECT   = []
    ∧ RULE.INDIRECT = [] )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Neighborhood: Type 0 (Non-Collapsed Node Without Incoming Ancestral Paths) Hypothesis (Top Formula) -/
def type0_hypothesis (RULE : Neighborhood) : Prop :=
    ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 ) ∧ ( RULE.CENTER.HYPOTHESIS = true )
  ∧ ( RULE.CENTER.COLLAPSED = false ) ∧ ( RULE.CENTER.PAST = [] )
  ∧ ( ∃(out_nbr : Nat),
      ∃(out_fml : Formula),
    ------------------------------------------------------
      ( out_nbr > 0 )
    ∧ RULE.INCOMING = []
    ∧ RULE.OUTGOING = [ edge RULE.CENTER
                             (node out_nbr (RULE.CENTER.LEVEL-1) out_fml false false [])
                             0
                             [RULE.CENTER.FORMULA] ]
    ∧ RULE.DIRECT   = []
    ∧ RULE.INDIRECT = [] )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Neighborhood: Type 2 (Non-Collapsed Node With Incoming Ancestral Paths) ⊇-Elimination -/
def type2_elimination (RULE : Neighborhood) : Prop :=
    ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 ) ∧ ( RULE.CENTER.HYPOTHESIS = false )
  ∧ ( RULE.CENTER.COLLAPSED = false ) ∧ ( RULE.CENTER.PAST = [] )
  ∧ ( ∃(inc_nbr out_nbr anc_nbr anc_lvl : Nat),
      ∃(antecedent out_fml anc_fml : Formula),
      ∃(major_hpt minor_hpt out_hpt : Bool),
      ∃(major_dep minor_dep : List Formula),
      ∃(past colour : Nat)(pasts colours : List Nat),
      ------------------------------------------------------
      ( inc_nbr > 0 ) ∧ ( out_nbr > 0 )
    ∧ ( anc_nbr > 0 ) ∧ ( anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL )
    ∧ ( colour ∈ (out_nbr::past::pasts) ) ∧ ( check_numbers (past::pasts) ) ∧ ( check_numbers (colour::colours) )
    ∧ RULE.INCOMING = [ edge (node (inc_nbr+1) (RULE.CENTER.LEVEL+1) (antecedent>>RULE.CENTER.FORMULA) major_hpt false []) /- Right Child & Major Premise -/
                             RULE.CENTER
                             0
                             #major_dep,
                        edge (node inc_nbr (RULE.CENTER.LEVEL+1) antecedent minor_hpt false [])                            /- Left Child & Minor Premise -/
                             RULE.CENTER
                             0
                             #minor_dep ]
    ∧ RULE.OUTGOING = [ edge RULE.CENTER
                             (node out_nbr (RULE.CENTER.LEVEL-1) out_fml out_hpt true (past::pasts))
                             0
                             (minor_dep ∪ major_dep) ]
    ∧ RULE.DIRECT   = [ path (node anc_nbr anc_lvl anc_fml false false [])
                             RULE.CENTER
                             (0::colour::colours) ]
    ∧ RULE.INDIRECT = [] )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Neighborhood: Type 2 (Non-Collapsed Node With Incoming Ancestral Paths) ⊇-Introduction -/
def type2_introduction (RULE : Neighborhood) : Prop :=
    ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 ) ∧ ( RULE.CENTER.HYPOTHESIS = false )
  ∧ ( RULE.CENTER.COLLAPSED = false ) ∧ ( RULE.CENTER.PAST = [] )
  ∧ ( ∃(inc_nbr out_nbr anc_nbr anc_lvl : Nat),
      ∃(antecedent consequent out_fml anc_fml : Formula),
      ∃(out_hpt : Bool),
      ∃(inc_dep : List Formula),
      ∃(past colour : Nat)(pasts colours : List Nat),
    ------------------------------------------------------
      ( RULE.CENTER.FORMULA = antecedent>>consequent )
    ∧ ( inc_nbr > 0 ) ∧ ( out_nbr > 0 )
    ∧ ( anc_nbr > 0 ) ∧ ( anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL )
    ∧ ( colour ∈ (out_nbr::past::pasts) ) ∧ ( check_numbers (past::pasts) ) ∧ ( check_numbers (colour::colours) )
    ∧ RULE.INCOMING = [ edge (node inc_nbr (RULE.CENTER.LEVEL+1) consequent false false [])  /- Unique Child & Sole Premise -/
                             RULE.CENTER
                             0
                             #inc_dep ]
    ∧ RULE.OUTGOING = [ edge RULE.CENTER
                             (node out_nbr (RULE.CENTER.LEVEL-1) out_fml out_hpt true (past::pasts))
                             0
                             (inc_dep − [antecedent]) ]
    ∧ RULE.DIRECT   = [ path (node anc_nbr anc_lvl anc_fml false false [])
                             RULE.CENTER
                             (0::colour::colours) ]
    ∧ RULE.INDIRECT = [] )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Neighborhood: Type 2 (Non-Collapsed Node With Incoming Ancestral Paths) Hypothesis (Top Formula) -/
def type2_hypothesis (RULE : Neighborhood) : Prop :=
    ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 ) ∧ ( RULE.CENTER.HYPOTHESIS = true )
  ∧ ( RULE.CENTER.COLLAPSED = false ) ∧ ( RULE.CENTER.PAST = [] )
  ∧ ( ∃(out_nbr anc_nbr anc_lvl : Nat),
      ∃(out_fml anc_fml : Formula),
      ∃(out_hpt : Bool),
      ∃(past colour : Nat)(pasts colours : List Nat),
    ------------------------------------------------------
      ( out_nbr > 0 )
    ∧ ( anc_nbr > 0 ) ∧ ( anc_lvl + List.length (0::colour::colours) = RULE.CENTER.LEVEL )
    ∧ ( colour ∈ (out_nbr::past::pasts) ) ∧ ( check_numbers (past::pasts) ) ∧ ( check_numbers (colour::colours) )
    ∧ RULE.INCOMING = []
    ∧ RULE.OUTGOING = [ edge RULE.CENTER
                             (node out_nbr (RULE.CENTER.LEVEL-1) out_fml out_hpt true (past::pasts))
                             0
                             [RULE.CENTER.FORMULA] ]
    ∧ RULE.DIRECT   = [ path (node anc_nbr anc_lvl anc_fml false false [])
                             RULE.CENTER
                             (0::colour::colours) ]
    ∧ RULE.INDIRECT = [] )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Neighborhood: Check Incoming Edges (Type 1 & 3) -/--------------------------------------------------------------------------------------------------------------------------
def type_incoming (RULE : Neighborhood) : Prop := ∀{INC : Deduction}, ( INC ∈ RULE.INCOMING ) → ( check INC RULE.CENTER RULE.INDIRECT )
  where check (INC : Deduction) (CENTER : Vertex) (INDIRECT : List Ancestral) : Prop :=
        /- Start Node: -/------------------------------------------------------------------------------------------------------------------------------------------------------
        ( ( INC.START.NUMBER > 0 ) ∧ ( INC.START.LEVEL = CENTER.LEVEL + 1 )
        ∧ ( INC.START.COLLAPSED = false ) ∧ ( INC.START.PAST = [] ) )
        /- End Node: -/--------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( INC.END = CENTER )
        /- Colours: -/---------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( INC.COLOUR = 0 )                                                                                                /- := Incoming Edge => -/
        /- Deduction-Ancestral Duo: -/-----------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ∃(colour : Nat)(colours : List Nat)(anc : Vertex), ( path anc INC.START (0::colour::colours) ∈ INDIRECT ) )     /- => Indirect Path => -/
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------

/- Neighborhood: Check Outgoing Edges (Type 1) -/------------------------------------------------------------------------------------------------------------------------------
def type_outgoing₁ (RULE : Neighborhood) : Prop := ∀{OUT : Deduction}, ( OUT ∈ RULE.OUTGOING ) → ( type_outgoing₁.check_h₁ OUT RULE.CENTER
                                                                                                 ∨ type_outgoing₁.check_ie₁ OUT RULE.CENTER RULE.INDIRECT )
  where check_h₁ (OUT : Deduction) (CENTER : Vertex) : Prop :=
        /- Type 1 Hypothesis -/------------------------------------------------------------------------------------------------------------------------------------------------
        ( CENTER.HYPOTHESIS = true )
        /- Start Node: -/------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.START = CENTER )
        /- End Node: -/--------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ( OUT.END.NUMBER > 0 ) ∧ ( OUT.END.LEVEL = CENTER.LEVEL - 1 )
        ∧ ( OUT.END.COLLAPSED = false ) ∧ ( OUT.END.PAST = [] ) )
        /- Colours: -/---------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.COLOUR = 0 )
        -----------------------------------------------------------------------------------------------------------------------------------------------------------------------
        check_ie₁ (OUT : Deduction) (CENTER : Vertex) (INDIRECT : List Ancestral) : Prop :=
        /- Type 1 Introduction & Elimination -/--------------------------------------------------------------------------------------------------------------------------------
        ( ( CENTER.HYPOTHESIS = false ) ∨ ( CENTER.COLLAPSED = true ) )
        /- Start Node: -/------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.START = CENTER )
        /- End Node: -/--------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ( OUT.END.NUMBER > 0 ) ∧ ( OUT.END.LEVEL = CENTER.LEVEL - 1 )
        ∧ ( OUT.END.COLLAPSED = false ) ∧ ( OUT.END.PAST = [] ) )
        /- Colours: -/---------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.COLOUR ∈ (CENTER.NUMBER::CENTER.PAST) )                                                                             /- := Outgoing Edge => -/
        /- Deduction-Ancestral Duo: -/-----------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ∃(inc : Vertex), ( path OUT.END inc [0, OUT.COLOUR] ∈ INDIRECT ) )                                                      /- => Indirect Path => -/
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------
/- Neighborhood: Check Outgoing Edges (Type 3) -/------------------------------------------------------------------------------------------------------------------------------
def type_outgoing₃ (RULE : Neighborhood) : Prop := ∀{OUT : Deduction}, ( OUT ∈ RULE.OUTGOING ) → ( ( type_outgoing₁.check_h₁ OUT RULE.CENTER
                                                                                                   ∨ type_outgoing₁.check_ie₁ OUT RULE.CENTER RULE.INDIRECT )
                                                                                                 ∨ ( type_outgoing₃.check_h₃ OUT RULE.CENTER RULE.DIRECT
                                                                                                   ∨ type_outgoing₃.check_ie₃ OUT RULE.CENTER RULE.INDIRECT ) )
  where check_h₃ (OUT : Deduction) (CENTER : Vertex) (DIRECT : List Ancestral) : Prop :=
        /- Type 3 Hypothesis -/------------------------------------------------------------------------------------------------------------------------------------------------
        ( CENTER.HYPOTHESIS = true )
        /- Start Node: -/------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.START = CENTER )
        /- End Node: -/--------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ( OUT.END.NUMBER > 0 ) ∧ ( OUT.END.LEVEL = CENTER.LEVEL - 1 )
        ∧ ( OUT.END.COLLAPSED = true ) ∧ ( ∃(past : Nat)(pasts : List Nat), ( check_numbers (past::pasts) )
                                                                          ∧ ( OUT.END.PAST = (past::pasts) ) ) )
        /- Colours: -/---------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.COLOUR ∈ (CENTER.NUMBER::CENTER.PAST) )                                                                             /- := Outgoing Edge => -/
        /- Deduction-Ancestral Duo: -/-----------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ∃(colours : List Nat)(anc : Vertex), ( path anc CENTER (OUT.COLOUR::colours) ∈ DIRECT ) )                               /- => Direct Path . -/
        -----------------------------------------------------------------------------------------------------------------------------------------------------------------------
        check_ie₃ (OUT : Deduction) (CENTER : Vertex) (INDIRECT : List Ancestral) : Prop :=
        /- Type 3 Introduction & Elimination -/--------------------------------------------------------------------------------------------------------------------------------
        ( ( CENTER.HYPOTHESIS = false ) ∨ ( CENTER.COLLAPSED = true ) )
        /- Start Node: -/------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.START = CENTER )
        /- End Node: -/--------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ( OUT.END.NUMBER > 0 ) ∧ ( OUT.END.LEVEL = CENTER.LEVEL - 1 )
        ∧ ( OUT.END.COLLAPSED = true ) ∧ ( ∃(past : Nat)(pasts : List Nat), ( check_numbers (past::pasts) )
                                                                          ∧ ( OUT.END.PAST = (past::pasts) ) ) )
        /- Colours: -/---------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( OUT.COLOUR ∈ (CENTER.NUMBER::CENTER.PAST) )                                                                             /- := Outgoing Edge => -/
        /- Deduction-Ancestral Duo: -/-----------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ∃(colours : List Nat)(inc anc : Vertex), ( path anc inc (0::OUT.COLOUR::colours) ∈ INDIRECT ) )                         /- => Indirect Path => -/
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------

/- Neighborhood: Check Direct Paths (Type 1 & 3) -/----------------------------------------------------------------------------------------------------------------------------
def type_direct (RULE : Neighborhood) : Prop := ∀{DIR : Ancestral}, ( DIR ∈ RULE.DIRECT ) → ( check DIR RULE.CENTER RULE.OUTGOING )
  where check (DIR : Ancestral) (CENTER : Vertex) (OUTGOING : List Deduction) : Prop :=
        /- Start Node: -/------------------------------------------------------------------------------------------------------------------------------------------------------
        ( ( DIR.START.NUMBER > 0 ) ∧ ( DIR.START.LEVEL ≤ CENTER.LEVEL - 1 ) ∧ ( DIR.START.HYPOTHESIS = false )
        ∧ ( DIR.START.COLLAPSED = false ) ∧ ( DIR.START.PAST = [] ) )
        /- End Node: -/--------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( DIR.END = CENTER )
        /- Colours: -/---------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( DIR.START.LEVEL + List.length (DIR.COLOURS) = CENTER.LEVEL )
      ∧ ( ∃(colour₁ colour₂ : Nat),
          ∃(colours : List Nat), ( check_numbers (colour₁::colour₂::colours) )
                               ∧ ( colour₁ ∈ (CENTER.NUMBER::CENTER.PAST) )
                               ∧ ( DIR.COLOURS = (colour₁::colour₂::colours) )                                                /- := Direct Path => -/
                                 /- Deduction-Ancestral Duo: -/----------------------------------------------------------------------------------------------------------------
                               ∧ ( ∃(out : Vertex),                                                                           /- => Outgoing Edge . -/
                                   ∃(dep_out : List Formula), ( out.COLLAPSED = true )
                                                            ∧ ( colour₂ ∈ (out.NUMBER::out.PAST) )
                                                            ∧ ( edge CENTER out colour₁ dep_out ∈ OUTGOING )
                                                            ∧ ( ∀{all_out : Deduction}, ( all_out ∈ OUTGOING ) →
                                                                                        ( ( all_out.COLOUR = colour₁ ) ↔ ( all_out = edge CENTER out colour₁ dep_out ) ) ) ) )
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------

/- Neighborhood: Check Indirect Paths (Type 1 & 3) -/--------------------------------------------------------------------------------------------------------------------------
def type_indirect (RULE : Neighborhood) : Prop := ∀{IND : Ancestral}, ( IND ∈ RULE.INDIRECT ) → ( check IND RULE.CENTER RULE.INCOMING RULE.OUTGOING )
  where check (IND : Ancestral) (CENTER : Vertex) (INCOMING OUTGOING : List Deduction) : Prop :=
        /- Start Node: -/------------------------------------------------------------------------------------------------------------------------------------------------------
        ( ( IND.START.NUMBER > 0 ) ∧ ( IND.START.LEVEL ≤ CENTER.LEVEL - 1 ) ∧ ( IND.START.HYPOTHESIS = false )
        ∧ ( IND.START.COLLAPSED = false ) ∧ ( IND.START.PAST = [] ) )
        /- End Node: -/--------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( ( IND.END.NUMBER > 0 ) ∧ ( IND.END.LEVEL = CENTER.LEVEL + 1 )
        ∧ ( IND.END.COLLAPSED = false ) ∧ ( IND.END.PAST = [] ) )
        /- Colours: -/---------------------------------------------------------------------------------------------------------------------------------------------------------
      ∧ ( IND.START.LEVEL + List.length (IND.COLOURS) = CENTER.LEVEL + 1 )
      ∧ ( ∃(colour : Nat),
          ∃(colours : List Nat), ( check_numbers (colour::colours) )
                               ∧ ( colour ∈ (CENTER.NUMBER::CENTER.PAST) )
                               ∧ ( IND.COLOURS = (0::colour::colours) )                                                         /- := Indirect Path => -/
                                 /- Deduction-Ancestral Trio: -/---------------------------------------------------------------------------------------------------------------
                               ∧ ( ∃(dep_inc : List Formula), ( edge IND.END CENTER 0 dep_inc ∈ INCOMING )                      /- => Incoming Edge => -/
                                                            ∧ ( ∀{all_inc : Deduction}, ( all_inc ∈ INCOMING ) →
                                                                                        ( ( all_inc.START = IND.END ) ↔ ( all_inc = edge IND.END CENTER 0 dep_inc ) ) ) )
                               ∧ ( ∃(out : Vertex),                                                                             /- => Outgoing Edge . -/
                                   ∃(dep_out : List Formula), ( ( colours = [] ) ↔ ( out = IND.START ) )
                                                            ∧ ( edge CENTER out colour dep_out ∈ OUTGOING )
                                                            ∧ ( ∀{all_out : Deduction}, ( all_out ∈ OUTGOING ) →
                                                                                        ( ( all_out.COLOUR = colour ) ↔ ( all_out = edge CENTER out colour dep_out ) ) ) ) )
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------

/- Neighborhood: Pre-Type 1 (Collapsed Nodes With Short Neighboring Ancestral Paths) Collapsed Node -/
def type1_pre_collapse (RULE : Neighborhood) : Prop :=
    /- Check Center -/-----------------------------------------------------------------------------------------------------------------------
    ( ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 )
    ∧ ( RULE.CENTER.COLLAPSED = false )
    ∧ ( RULE.CENTER.PAST = [] )
    /- Check Deduction Edges -/--------------------------------------------------------------------------------------------------------------
    ∧ ( ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) )
    ∧ ( List.length (RULE.INCOMING) ≤ 2 )
    ∧ ( ∃(out : Deduction), ( RULE.OUTGOING = [out] ) )
    ∧ ( ∀{OUT₁ OUT₂ : Deduction}, ( OUT₁ ∈ RULE.OUTGOING ) →
                                  ( OUT₂ ∈ RULE.OUTGOING ) →
                                  ( OUT₁.COLOUR > 0 ∨ OUT₂.COLOUR > 0 ) →
                                  ( ( OUT₁.COLOUR = OUT₂.COLOUR ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check Ancestral Paths -/--------------------------------------------------------------------------------------------------------------
    ∧ ( RULE.DIRECT = [] )
    ∧ ( ∀{ind₁ ind₂ : Ancestral}, ( ind₁ ∈ RULE.INDIRECT ) →
                                  ( ind₂ ∈ RULE.INDIRECT ) → ( ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) ) )
    ∧ ( List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) )
    ∧ ( ∀{ind : Ancestral}, ( ind ∈ RULE.INDIRECT ) → ( ind.COLOURS = [0, RULE.CENTER.NUMBER] ) )
    /- Generic Properties -/-----------------------------------------------------------------------------------------------------------------
    ∧ ( type_incoming RULE ) ∧ ( type_outgoing₁ RULE )
    ∧ ( type_indirect RULE ) )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Neighborhood: Type 1 (Collapsed Nodes With Short Neighboring Ancestral Paths) Collapsed Node -/
def type1_collapse (RULE : Neighborhood) : Prop :=
    /- Check Center -/-----------------------------------------------------------------------------------------------------------------------
    ( ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 )
    ∧ ( RULE.CENTER.COLLAPSED = true )
    ∧ ( ∃(past : Nat)(pasts : List Nat), ( check_numbers (past::pasts) )
                                       ∧ ( RULE.CENTER.PAST = (past::pasts) ) )
    /- Check Deduction Edges -/--------------------------------------------------------------------------------------------------------------
    ∧ ( ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) )
    ∧ ( ∃(out : Deduction)(outs : List Deduction), ( RULE.OUTGOING = (out::outs) ) )
    ∧ ( ∀{OUT₁ OUT₂ : Deduction}, ( OUT₁ ∈ RULE.OUTGOING ) →
                                  ( OUT₂ ∈ RULE.OUTGOING ) →
                                  ( OUT₁.COLOUR > 0 ∨ OUT₂.COLOUR > 0 ) →
                                  ( ( OUT₁.COLOUR = OUT₂.COLOUR ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check Ancestral Paths -/--------------------------------------------------------------------------------------------------------------
    ∧ ( RULE.DIRECT = [] )
    ∧ ( List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) )
    ∧ ( ∀{ind : Ancestral}, ( ind ∈ RULE.INDIRECT ) → ( ∃(colour : Nat), ( ind.COLOURS = [0, colour] ) ) )
    /- Generic Properties -/-----------------------------------------------------------------------------------------------------------------
    ∧ ( type_incoming RULE ) ∧ ( type_outgoing₁ RULE )
    ∧ ( type_indirect RULE ) )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Neighborhood: Pre-Type 3 (Collapsed Nodes With Long Neighboring Ancestral Paths) Collapsed Node -/
def type3_pre_collapse (RULE : Neighborhood) : Prop :=
    /- Check Center -/-----------------------------------------------------------------------------------------------------------------------
    ( ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 )
    ∧ ( RULE.CENTER.COLLAPSED = false )
    ∧ ( RULE.CENTER.PAST = [] )
    /- Check Deduction Edges -/--------------------------------------------------------------------------------------------------------------
    ∧ ( ( RULE.INCOMING = [] ) ↔ ( RULE.CENTER.HYPOTHESIS = true ) )
    ∧ ( List.length (RULE.INCOMING) ≤ 2 )
    ∧ ( ∃(out : Deduction), ( RULE.OUTGOING = [out] ) )
    ∧ ( ∀{OUT₁ OUT₂ : Deduction}, ( OUT₁ ∈ RULE.OUTGOING ) →
                                  ( OUT₂ ∈ RULE.OUTGOING ) →
                                  ( OUT₁.COLOUR > 0 ∨ OUT₂.COLOUR > 0 ) →
                                  ( ( OUT₁.COLOUR = OUT₂.COLOUR ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check Ancestral Paths -/--------------------------------------------------------------------------------------------------------------
    ∧ ( ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) )
    ∧ ( ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) )
    ∧ ( ( RULE.DIRECT = [] ) ∨ ( ∃(dir : Ancestral), ( RULE.DIRECT = [dir] ) ) )
    ∧ ( ∀{ind₁ ind₂ : Ancestral}, ( ind₁ ∈ RULE.INDIRECT ) →
                                  ( ind₂ ∈ RULE.INDIRECT ) → ( ( ind₁.COLOURS = ind₂.COLOURS ) ↔ ( ind₁.START = ind₂.START ) ) )
    ∧ ( List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) )
    /- Generic Properties -/-----------------------------------------------------------------------------------------------------------------
    ∧ ( type_incoming RULE ) ∧ ( type_outgoing₃ RULE )
    ∧ ( type_direct RULE ) ∧ ( type_indirect RULE ) )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Neighborhood: Type 3 (Collapsed Nodes With Long Neighboring Ancestral Paths) Collapsed Node -/
def type3_collapse (RULE : Neighborhood) : Prop :=
    /- Check Center -/-----------------------------------------------------------------------------------------------------------------------
    ( ( RULE.CENTER.NUMBER > 0 ) ∧ ( RULE.CENTER.LEVEL > 0 )
    ∧ ( RULE.CENTER.COLLAPSED = true )
    ∧ ( ∃(past : Nat)(pasts : List Nat), ( check_numbers (past::pasts) )
                                       ∧ ( RULE.CENTER.PAST = (past::pasts) ) )
    /- Check Deduction Edges -/--------------------------------------------------------------------------------------------------------------
    ∧ ( ( RULE.INCOMING = [] ) → ( RULE.CENTER.HYPOTHESIS = true ) )
    ∧ ( ∃(out : Deduction)(outs : List Deduction), ( RULE.OUTGOING = (out::outs) ) )
    ∧ ( ∀{OUT₁ OUT₂ : Deduction}, ( OUT₁ ∈ RULE.OUTGOING ) →
                                  ( OUT₂ ∈ RULE.OUTGOING ) →
                                  ( OUT₁.COLOUR > 0 ∨ OUT₂.COLOUR > 0 ) →
                                  ( ( OUT₁.COLOUR = OUT₂.COLOUR ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check Ancestral Paths -/--------------------------------------------------------------------------------------------------------------
    ∧ ( ( RULE.CENTER.HYPOTHESIS = false ) → ( RULE.DIRECT = [] ) )
    ∧ ( ( RULE.DIRECT ≠ [] ) → ( RULE.CENTER.HYPOTHESIS = true ) )
    ∧ ( List.length (RULE.INDIRECT) = List.length (RULE.INCOMING) )
    /- Generic Properties -/-----------------------------------------------------------------------------------------------------------------
    ∧ ( type_incoming RULE ) ∧ ( type_outgoing₃ RULE )
    ∧ ( type_direct RULE ) ∧ ( type_indirect RULE ) )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- End -/
