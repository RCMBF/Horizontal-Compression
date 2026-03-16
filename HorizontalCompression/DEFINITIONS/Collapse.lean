import Init
import BASICS.MyList
import BASICS.MyTypes
import DEFINITIONS.PreCollapse

/- Collapse Methods -/
/- Collapse: NODE × NODE → NODE -/-----------------------------------------------------------------------------------------------------------
def collapse.center (LEFT RIGHT : Vertex) : Vertex :=
    node ( LEFT.NUMBER )
         ( LEFT.LEVEL )
         ( LEFT.FORMULA )
         ( LEFT.HYPOTHESIS || RIGHT.HYPOTHESIS )
         ( true )
         ( RIGHT.NUMBER :: LEFT.PAST )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Rewrite: Deduction Edge End -/------------------------------------------------------------------------------------------------------------
def collapse.rewrite_incoming (COLLAPSE : Vertex) (EDGES : List Deduction) : List Deduction :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( edge EDGE.START COLLAPSE EDGE.COLOUR EDGE.DEPENDENCY ) :: ( rewrite_incoming COLLAPSE EDGES )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Rewrite: Deduction Edge Start -/----------------------------------------------------------------------------------------------------------
def collapse.rewrite_outgoing (COLLAPSE : Vertex) (EDGES : List Deduction) : List Deduction :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( edge COLLAPSE EDGE.END EDGE.COLOUR EDGE.DEPENDENCY ) :: ( rewrite_outgoing COLLAPSE EDGES )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Rewrite: Ancestral Edge End -/------------------------------------------------------------------------------------------------------------
def collapse.rewrite_direct (COLLAPSE : Vertex) (PATHS : List Ancestral) : List Ancestral :=
    match PATHS with
    | [] => []
    | (PATH::PATHS) => ( path PATH.START COLLAPSE PATH.COLOURS ) :: ( rewrite_direct COLLAPSE PATHS )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Collapse Definitions (Collapses a Single Pair of Nodes) -/
/- Collapse: RULE × RULE → Neighborhood -/---------------------------------------------------------------------------------------------------
def collapse (RULEᵤ RULEᵥ : Neighborhood) : Neighborhood :=
    rule ( collapse.center RULEᵤ.CENTER RULEᵥ.CENTER )
         ( collapse.rewrite_incoming (collapse.center RULEᵤ.CENTER RULEᵥ.CENTER) RULEᵥ.INCOMING
        ++ collapse.rewrite_incoming (collapse.center RULEᵤ.CENTER RULEᵥ.CENTER) RULEᵤ.INCOMING )
         ( collapse.rewrite_outgoing (collapse.center RULEᵤ.CENTER RULEᵥ.CENTER) RULEᵥ.OUTGOING
        ++ collapse.rewrite_outgoing (collapse.center RULEᵤ.CENTER RULEᵥ.CENTER) RULEᵤ.OUTGOING )
         ( collapse.rewrite_direct (collapse.center RULEᵤ.CENTER RULEᵥ.CENTER) RULEᵥ.DIRECT
        ++ collapse.rewrite_direct (collapse.center RULEᵤ.CENTER RULEᵥ.CENTER) RULEᵤ.DIRECT )
         ( RULEᵥ.INDIRECT
        ++ RULEᵤ.INDIRECT )
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Collapse: NODE × NODE × DLDS → Neighborhood -/--------------------------------------------------------------------------------------------
def collapse_rule (U V : Vertex) (DLDS : Graph) : Neighborhood := collapse ( pre_collapse (get_rule U DLDS) )
                                                                           ( pre_collapse (get_rule V DLDS) )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Is-Collapse Methods (DLDS) -/
/- Updade: Deduction Edge End -/------------------------------------------------------------------------------------------------------------
def is_collapse.update_edges_end (OLD NEW : Vertex) (EDGES : List Deduction) : List Deduction :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( loop OLD NEW EDGE ) :: ( update_edges_end OLD NEW EDGES )
  where loop (OLD NEW : Vertex) (EDGE : Deduction) : Deduction :=
        edge EDGE.START
            (if EDGE.END = OLD then NEW else EDGE.END)
            EDGE.COLOUR
            EDGE.DEPENDENCY
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Updade: Deduction Edge Start -/----------------------------------------------------------------------------------------------------------
def is_collapse.update_edges_start (OLD NEW : Vertex) (EDGES : List Deduction) : List Deduction :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( loop OLD NEW EDGE ) :: ( update_edges_start OLD NEW EDGES )
  where loop (OLD NEW : Vertex) (EDGE : Deduction) : Deduction :=
        edge (if EDGE.START = OLD then NEW else EDGE.START)
             EDGE.END
             EDGE.COLOUR
             EDGE.DEPENDENCY
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Updade: Ancestral Edge End -/------------------------------------------------------------------------------------------------------------
def is_collapse.update_paths_end (OLD NEW : Vertex) (PATHS : List Ancestral) : List Ancestral :=
    match PATHS with
    | [] => []
    | (PATH::PATHS) => ( loop OLD NEW PATH ) :: ( update_paths_end OLD NEW PATHS )
  where loop (OLD NEW : Vertex) (PATH : Ancestral) : Ancestral :=
        path PATH.START
             (if PATH.END = OLD then NEW else PATH.END)
             PATH.COLOURS
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Updade: Deduction Edge Start -/----------------------------------------------------------------------------------------------------------
def is_collapse.update_paths_start (OLD NEW : Vertex) (PATHS : List Ancestral) : List Ancestral :=
    match PATHS with
    | [] => []
    | (PATH::PATHS) => ( loop OLD NEW PATH ) :: ( update_paths_start OLD NEW PATHS )
  where loop (OLD NEW : Vertex) (PATH : Ancestral) : Ancestral :=
        path (if PATH.START = OLD then NEW else PATH.START)
             PATH.END
             PATH.COLOURS
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Is-Collapse: Vertex × Vertex × Graph × Graph → Prop -/-------------------------------------------------------------------------------------------
def Graph.is_collapse (U V : Vertex) : Graph → Graph → Prop
                /- Incoming Nodes -/-------------------------------------------------------------------------------------------------------------
                /- Above & Right Side (Collapsed Child) -/---------------------------------------------------------------------------------------
| CLPS, DLDS => ( ∀{inc : Deduction}, ( U.COLLAPSED = true ) →
                                      ( inc ∈ get_rule.incoming U DLDS ) →
                  ---------------------------------------------------------------------
                  ( get_rule inc.START CLPS = rule ( inc.START )
                                                   ( get_rule.incoming inc.START DLDS )
                /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (get_rule.outgoing inc.START DLDS) )
                /- Direct Inc ∈ Indirect UV -/     ( get_rule.direct inc.START DLDS )
                                                   ( get_rule.indirect inc.START DLDS ) ) )
                ---------------------------------------------------------------------------------------------------------------------------------
                /- Aboce & Right Side (Non-Collapsed Child) -/-----------------------------------------------------------------------------------
              ∧ ( ∀{inc : Deduction}, ( U.COLLAPSED = false ) →
                                      ( inc ∈ get_rule.incoming U DLDS ) →
                  ---------------------------------------------------------------------
                  ( get_rule inc.START CLPS = rule ( inc.START )
                                                   ( get_rule.incoming inc.START DLDS )
                /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (get_rule.outgoing inc.START DLDS) )
                /- Direct Inc ∈ Indirect UV -/     ( get_rule.direct.loop ( inc.START )
                                                                          ( pre_collapse.indirect ( U.NUMBER )
                                                                                                  ( U.HYPOTHESIS )
                                                                                                  ( get_rule.incoming U DLDS )
                                                                                                  ( get_rule.outgoing U DLDS )
                                                                                                  ( get_rule.direct U DLDS ) ) )
                                                   ( get_rule.indirect inc.START DLDS ) ) )
                ---------------------------------------------------------------------------------------------------------------------------------
                /- Above & Left Side -/----------------------------------------------------------------------------------------------------------
              ∧ ( ∀{inc : Deduction}, ( inc ∈ get_rule.incoming V DLDS ) →
                  ---------------------------------------------------------------------
                  ( get_rule inc.START CLPS = rule ( inc.START )
                                                   ( get_rule.incoming inc.START DLDS )
                /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end V (collapse.center U V) (get_rule.outgoing inc.START DLDS) )
                /- Direct Inc ∈ Indirect UV -/     ( get_rule.direct.loop ( inc.START )
                                                                          ( pre_collapse.indirect ( V.NUMBER )
                                                                                                  ( V.HYPOTHESIS )
                                                                                                  ( get_rule.incoming V DLDS )
                                                                                                  ( get_rule.outgoing V DLDS )
                                                                                                  ( get_rule.direct V DLDS ) ) )
                                                   ( get_rule.indirect inc.START DLDS ) ) )
    ---------------------------------------------------------------------------------------------------------------------------------------------

/- End -/
