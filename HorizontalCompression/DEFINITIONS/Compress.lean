import Init
import BASICS.MyList
import BASICS.MyTypes
import DEFINITIONS.PreCollapse
import DEFINITIONS.Collapse

/- Compress Methods -/
/- Convert: NODES × DLDS → Neighborhood -/----------------------------------------------------------
def get_rules (NODES : List Vertex) (DLDS : Graph) : List Neighborhood :=
    match NODES with
    | [] => []
    | (NODE::NODES) => ( get_rule NODE DLDS :: get_rules NODES DLDS )
    ------------------------------------------------------------------------------------------------
/- Compress: RULES → List Neighborhood -/----------------------------------------------------------------------------------------------------
def pre_compress (RULES : List Neighborhood) : List Neighborhood :=
    match RULES with
    | [] => []
    | (RULE::RULES) => ( pre_collapse RULE ) :: ( pre_compress RULES )
/- Compress: RULES → Neighborhood -/---------------------------------------------------------------------------------------------------------
def compress (RULES : List Neighborhood) : Neighborhood :=
    match RULES with
    | [] => rule (node 0 0 #"" false false []) [] [] [] []
    | [RULE] => RULE
    | (RULE₁::RULE₂::RULES) => compress ((collapse ( RULE₁ ) ( RULE₂ ))::RULES)
    termination_by RULES.length
    decreasing_by
      simp only [List.length];
      simp +arith;
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Compression Definitions (Collapses Multiple Pairs of Nodes) -/
/- Compress: NODES × DLDS → Neighborhood -/--------------------------------------------------------------------------------------------------
def compress_rule (NODES : List Vertex) (DLDS : Graph) : Neighborhood := compress ( pre_compress (get_rules NODES DLDS) )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Convert: RULE × DLDS → Graph -/------------------------------------------------------------------
def pop_rules (DLDS : Graph) (RULES : List Neighborhood) : Graph :=
    dlds ( List.removeAll DLDS.NODES ( center RULES ) )
         ( List.removeAll DLDS.EDGES ( incoming RULES ++ outgoing RULES ) )
         ( List.removeAll DLDS.PATHS ( direct RULES ++ indirect RULES ) )
    where center (RULES : List Neighborhood) : List Vertex :=
          match RULES with
          | [] => []
          | (RULE::RULES) => ( RULE.CENTER :: center RULES )
          incoming (RULES : List Neighborhood) : List Deduction :=
          match RULES with
          | [] => []
          | (RULE::RULES) => ( RULE.INCOMING ++ incoming RULES )
          outgoing (RULES : List Neighborhood) : List Deduction :=
          match RULES with
          | [] => []
          | (RULE::RULES) => ( RULE.OUTGOING ++ outgoing RULES )
          direct (RULES : List Neighborhood) : List Ancestral :=
          match RULES with
          | [] => []
          | (RULE::RULES) => ( RULE.DIRECT ++ direct RULES )
          indirect (RULES : List Neighborhood) : List Ancestral :=
          match RULES with
          | [] => []
          | (RULE::RULES) => ( RULE.INDIRECT ++ indirect RULES )
    ------------------------------------------------------------------------------------------------
/- Convert: RULE × DLDS → Graph -/------------------------------------------------------------------
def set_rule (DLDS : Graph) (RULE : Neighborhood) : Graph :=
    dlds ( RULE.CENTER :: DLDS.NODES )
         ( RULE.INCOMING ++ RULE.OUTGOING ++ DLDS.EDGES )
         ( RULE.DIRECT ++ RULE.INDIRECT ++ DLDS.PATHS )
    ------------------------------------------------------------------------------------------------

/- Collapse: NODE × NODE × DLDS → Graph -/----------------------------------------------------------
def collapse_nodes (U V : Vertex) (DLDS : Graph) : Graph :=
    set_rule ( pop_rules DLDS ( get_rules [U,V] DLDS ) )
             ( collapse_rule U V DLDS )
    ------------------------------------------------------------------------------------------------
/- Compress: NODE × DLDS → Graph -/-----------------------------------------------------------------
def compress_nodes (NODES : List Vertex) (DLDS : Graph) : Graph :=
    set_rule ( pop_rules DLDS ( get_rules NODES DLDS ) )
             ( compress_rule NODES DLDS )
    ------------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------

/- DLDS-Graph Methods -/
/- Get: DLDS → Nat -/-------------------------------------------------------------------------------
def get_levels (DLDS : Graph) : List Nat := loop [] DLDS.NODES
    where loop (LEVELS : List Nat) (NODES : List Vertex) : List Nat :=
          match NODES with
          | [] => LEVELS
          | (NODE::NODES) => if   ( NODE.LEVEL ∈ LEVELS )
                             then ( loop LEVELS NODES )
                             else ( loop (NODE.LEVEL :: LEVELS) NODES )
/- Get: DLDS → Formula -/---------------------------------------------------------------------------
def get_labels (DLDS : Graph) : List Formula := loop [] DLDS.NODES
    where loop (LABELS : List Formula) (NODES : List Vertex) : List Formula :=
          match NODES with
          | [] => LABELS
          | (NODE::NODES) => if   ( NODE.FORMULA ∈ LABELS )
                             then ( loop LABELS NODES )
                             else ( loop (NODE.FORMULA :: LABELS) NODES )
    ------------------------------------------------------------------------------------------------

/- Convert: DLDS → Vertex -/------------------------------------------------------------------------
def repeated_nodes_vertex (DLDS : Graph) : List (List (List Vertex)) := loop₀ ( get_levels DLDS )
                                                                              ( get_labels DLDS )
                                                                              ( DLDS.NODES )
        -- Separates the DLDS by level:
  where loop₀ (LEVELS : List Nat) (LABELS : List Formula) (NODES : List Vertex) : List (List (List Vertex)) :=
        match LEVELS with
        | [] => []
        | (LEVEL::LEVELS) => if   ( loop₁ LEVEL LABELS NODES ≠ [] )
                             then ( loop₁ LEVEL LABELS NODES ) :: ( loop₀ LEVELS LABELS NODES )
                             else ( loop₀ LEVELS LABELS NODES )
        -- Separates levels by label:
        loop₁ (LEVEL : Nat) (LABELS : List Formula) (NODES : List Vertex) : List (List Vertex) :=
        match LABELS with
        | [] => []
        | (LABEL::LABELS) => if   ( loop₂ LEVEL LABEL [] NODES ≠ [] )
                             then ( loop₂ LEVEL LABEL [] NODES ) :: ( loop₁ LEVEL LABELS NODES )
                             else ( loop₁ LEVEL LABELS NODES )
        -- Gives the collapsable nodes in LEVEL of DLDS:
        loop₂ (LEVEL : Nat) (LABEL : Formula) (NODES₁ NODES₂ : List Vertex) : List Vertex :=
        match NODES₁, NODES₂ with
        | _, [] => []
        | NODES₁, (NODE::NODES₂) => if   ( NODE.LEVEL = LEVEL )
                                      && ( NODE.FORMULA = LABEL )
                                      && ( loop₃ NODE (NODES₁ ++ NODES₂) )
                                    then ( NODE ) :: ( loop₂ LEVEL LABEL (List.concat NODES₁ NODE) NODES₂ )
                                    else ( loop₂ LEVEL LABEL (List.concat NODES₁ NODE) NODES₂ )
        -- Checks if NODE is collapsable:
        loop₃ (NODE : Vertex) (NODESₓ : List Vertex) : Bool :=
        match NODESₓ with
        | [] => false
        | (NODEₓ::NODESₓ) => ( NODE.LEVEL = NODEₓ.LEVEL
                            && NODE.FORMULA = NODEₓ.FORMULA )
                          || ( loop₃ NODE NODESₓ )
    ------------------------------------------------------------------------------------------------

/- DLDS-Graph Definitions -/
/- HC Algorithm: Convert: DLDS → DLDS -/------------------------------------------------------------
def compress_nodes_graph (DLDS : Graph) : Graph := loop₀ ( DLDS )
                                                         ( repeated_nodes_vertex DLDS )
  where loop₀ (DLDS : Graph) (LEVELS : List (List (List Vertex))) : Graph :=
        match LEVELS with
        | [] => DLDS
        | (LEVEL::LEVELS) => loop₀ ( loop₁ DLDS LEVEL ) LEVELS
        loop₁ (DLDS : Graph) (FORMULAS : List (List Vertex)) : Graph :=
        match FORMULAS with
        | [] => DLDS
        | (FORMULA::FORMULAS) => loop₁ ( compress_nodes FORMULA DLDS ) FORMULAS
    ------------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------

/- Misc. Definitions -/
/- Collapse: NUMBER × DLDS → Vertex -/--------------------------------------------------------------
def get_first_vertex (NUMBER : Nat) (DLDS : Graph) : Vertex :=
    loop NUMBER DLDS.NODES
    where loop (NUMBER : Nat) (NODES : List Vertex) : Vertex :=
          match NODES with
          | [] => node 0 0 #"" false false []
          | (NODE::NODES) => if   ( NODE.NUMBER = NUMBER )
                             then ( NODE )
                             else ( loop NUMBER NODES )
/- Collapse: Nat × Nat × Graph → Graph -/-----------------------------------------------------------
def collapse_nodes_nat (U V : Nat) (DLDS : Graph) : Graph := collapse_nodes ( get_first_vertex U DLDS )
                                                                            ( get_first_vertex V DLDS )
                                                                            ( DLDS )
        --------------------------------------------------------------------------------------------

/- Printable Definitions -/
/- Print: DLDS → String -/--------------------------------------------------------------------------
def repeated_nodes_string (DLDS : Graph) : List (List (List String)) := loop₀ ( repeated_nodes_vertex DLDS )
  where loop₀ (NODES : List (List (List Vertex))) : List (List (List String)) :=
        match NODES with
        | [] => []
        | (NODE::NODES) => ( loop₁ NODE )
                        :: ( loop₀ NODES )
        loop₁ (NODES : List (List Vertex)) : List (List String) :=
        match NODES with
        | [] => []
        | (NODE::NODES) => ( loop₂ NODE )
                        :: ( loop₁ NODES )
        loop₂ (NODES : List Vertex) : List String :=
        match NODES with
        | [] => []
        | (NODE::NODES) => ( loop₃ NODE )
                        :: ( loop₂ NODES )
        loop₃ (NODE : Vertex) : String := NODE.LEVEL.repr ++ "-"
                                       ++ NODE.NUMBER.repr ++ "-"
                                       ++ NODE.FORMULA.repr
/- Print: DLDS → String -/--------------------------------------------------------------------------
def check_sub_graph (DLDS₁ DLDS₂ : Graph) : List Bool := [ nodes DLDS₁.NODES DLDS₂.NODES ,
                                                           edges DLDS₁.EDGES DLDS₂.EDGES ,
                                                           paths DLDS₁.PATHS DLDS₂.PATHS ]
  where nodes (NODES₁ NODES₂ : List Vertex) : Bool :=
        match NODES₁ with
        | [] => True
        | (NODE₁::NODES₁) => ( NODE₁ ∈ NODES₂ )
                           ∧ ( nodes NODES₁ NODES₂ )
        edges (EDGES₁ EDGES₂ : List Deduction) : Bool :=
        match EDGES₁ with
        | [] => True
        | (EDGE₁::EDGES₁) => ( EDGE₁ ∈ EDGES₂ )
                           ∧ ( edges EDGES₁ EDGES₂ )
        paths (PATHS₁ PATHS₂ : List Ancestral) : Bool :=
        match PATHS₁ with
        | [] => True
        | (PATH₁::PATHS₁) => ( PATH₁ ∈ PATHS₂ )
                           ∧ ( paths PATHS₁ PATHS₂ )
        --------------------------------------------------------------------------------------------

/- Printable Definitions -/
/- Print: String → DLDS -/--------------------------------------------------------------------------
def set_proof_tree (DLDS : Graph) : List (List (List String)) := loop₀ ( repeated_nodes_vertex DLDS )
  where loop₀ (NODES : List (List (List Vertex))) : List (List (List String)) :=
        match NODES with
        | [] => []
        | (NODE::NODES) => ( loop₁ NODE )
                        :: ( loop₀ NODES )
        loop₁ (NODES : List (List Vertex)) : List (List String) :=
        match NODES with
        | [] => []
        | (NODE::NODES) => ( loop₂ NODE )
                        :: ( loop₁ NODES )
        loop₂ (NODES : List Vertex) : List String :=
        match NODES with
        | [] => []
        | (NODE::NODES) => ( loop₃ NODE )
                        :: ( loop₂ NODES )
        loop₃ (NODE : Vertex) : String := NODE.LEVEL.repr ++ "-"
                                       ++ NODE.NUMBER.repr ++ "-"
                                       ++ NODE.FORMULA.repr
        --------------------------------------------------------------------------------------------

/- End -/
