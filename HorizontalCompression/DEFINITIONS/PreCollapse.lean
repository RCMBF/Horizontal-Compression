import Init
import BASICS.MyList
import BASICS.MyTypes

/- Pre-Collapse Methods -/
/- Paint: Deduction Edge -/------------------------------------------------------------------------------------------------------------------
def pre_collapse.outgoing (COLOUR : Nat) (HYPOTHESIS : Bool) (OUTGOING : List Deduction) (DIRECT : List Ancestral) : List Deduction :=
    match HYPOTHESIS, OUTGOING, DIRECT with
    | _, [], _ => panic! "Zero Outgoing Edges!!!"
    | _, (_::_::_), _ => panic! "Multiple Outgoing Edges!!!"
    | _, _, (_::_::_) => panic! "Multiple Direct Paths!!!"
    -- Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Return Outgoing Edge (Unpainted)
    | true, [_], [] => OUTGOING
    -- Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Return Outgoing Edge (Painted)
    | true, [OUT], [_] => [ edge OUT.START OUT.END COLOUR OUT.DEPENDENCY ]
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Return Outgoing Edge (Painted)
    | false, [OUT], [] => [ edge OUT.START OUT.END COLOUR OUT.DEPENDENCY ]
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Return Outgoing Edge (Painted)
    | false, [OUT], [_] => [ edge OUT.START OUT.END COLOUR OUT.DEPENDENCY ]
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Rewrite: Ancestral Paths -/---------------------------------------------------------------------------------------------------------------
def pre_collapse.direct (COLOUR : Nat) (HYPOTHESIS : Bool) (DIRECT : List Ancestral) : List Ancestral :=
    match HYPOTHESIS, DIRECT with
    | _, (_::_::_) => panic! "Multiple Direct Paths!!!"
    -- Hypothesis ∧ Zero Direct Paths => Return Nothing
    | true, [] => []
    -- Hypothesis ∧ Single Direct Path => Paint Direct Path
    | true, [PATH] => paint COLOUR PATH
    -- Non-Hypothesis ∧ Zero Direct Paths => Return Nothing
    | false, [] => []
    -- Non-Hypothesis ∧ Single Direct Path => Return Nothing
    | false, [_] => []
  where paint (COLOUR : Nat) (PATH : Ancestral) : List Ancestral :=
        match PATH.COLOURS with
        | [] => panic! "Blank Path!!!"
        | ((_+1)::_) => panic! "Broken Path!!!"
        -- Correctly Colored Path => Return Indirect Path(s)
        | (0::COLOURS) => [ path PATH.START PATH.END (COLOUR::COLOURS) ]
    -----------------------------------------------------------------------------------------------------------------------------------------
/- Create: Ancestral Paths -/----------------------------------------------------------------------------------------------------------------
def pre_collapse.indirect (COLOUR : Nat) (HYPOTHESIS : Bool) (INCOMING OUTGOING : List Deduction) (DIRECT : List Ancestral) : List Ancestral :=
    match HYPOTHESIS, INCOMING, OUTGOING, DIRECT with
    | true, (_::_), _, _ => panic! "Hypothesis With Incoming Edge(s)!!!"
    | false, [], _, _ => panic! "Non-Hypothesis Without Incoming Edge(s)"
    | _, _, [], _ => panic! "Zero Outgoing Edges!!!"
    | _, _, (_::_::_), _ => panic! "Multiple Outgoing Edges!!!"
    | _, _, _, (_::_::_) => panic! "Multiple Direct Paths!!!"
    -- Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Return Nothing
    | true, _, [_], [] => []
    -- Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Return Nothing
    | true, _, [_], [_] => []
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Create Indirect Path(s)
    | false, (_::_), [OUT], [] => create COLOUR INCOMING OUT
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Move-Up Direct Path(s)
    | false, (_::_), [_], [PATH] => move_up COLOUR INCOMING PATH
  where create (COLOUR : Nat) (INCOMING : List Deduction) (OUT : Deduction) : List Ancestral :=
        match INCOMING with
        | [] => []
        | (IN::INS) => ( path OUT.END IN.START [0, COLOUR] )
                    :: ( create COLOUR INS OUT )
        move_up (COLOUR : Nat) (INCOMING : List Deduction) (PATH : Ancestral) : List Ancestral :=
        match INCOMING, PATH with
        | _, (path _ _ []) => panic! "Blank Path!!!"
        -- Colored Path => Return Indirect Path(s)
        | [], (path _ _ (_::_)) => []
        | (IN::INS), (path _ _ (ZERO::COLOURS)) => ( path PATH.START IN.START (ZERO::COLOUR::COLOURS) )
                                                :: ( move_up COLOUR INS PATH )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- Pre-Collapse Definitions -/
/- Pre-Collapse: Neighborhood → Neighborhood -/----------------------------------------------------------------------------------------------
def pre_collapse (RULE : Neighborhood) : Neighborhood :=
    match RULE.CENTER.COLLAPSED with
    | true => RULE
    | false => rule ( RULE.CENTER )
                    ( RULE.INCOMING )
                    ( pre_collapse.outgoing RULE.CENTER.NUMBER RULE.CENTER.HYPOTHESIS RULE.OUTGOING RULE.DIRECT )
                    ( pre_collapse.direct RULE.CENTER.NUMBER RULE.CENTER.HYPOTHESIS RULE.DIRECT )
                    ( pre_collapse.indirect RULE.CENTER.NUMBER RULE.CENTER.HYPOTHESIS RULE.INCOMING RULE.OUTGOING RULE.DIRECT )
    -----------------------------------------------------------------------------------------------------------------------------------------

/- End -/
