import Init

/- Types -/
/- Dag-Like Derivability Structure -/
/- DLDS: Labels -/
inductive Formula where
| atom (SYMBOL : String) : Formula
| implication (ANTECEDENT CONSEQUENT : Formula) : Formula
export Formula (atom implication)
prefix:max "#" => Formula.atom
infixl:66 ">>" => Formula.implication
def Formula.repr (FORMULA : Formula) : String :=
    match FORMULA with
    | (atom SYMBOL) => "#" ++ SYMBOL
    | (implication ANTECEDENT CONSEQUENT) => (Formula.repr ANTECEDENT)
                                          ++ ">>"
                                          ++ (Formula.repr CONSEQUENT)
instance : Repr Formula where reprPrec formula _ := Formula.repr formula
/- DLDS: Vertices -/
structure Vertex where
node :: (NUMBER : Nat)
        (LEVEL : Nat)
        (FORMULA : Formula)
        (HYPOTHESIS : Bool)
        (COLLAPSED : Bool)
        (PAST : List Nat)   /- Temporary Collapse Metadata -/
deriving Repr
export Vertex (node)
/- DLDS: Deduction Edges -/
structure Deduction where
edge :: (START : Vertex)
        (END : Vertex)
        (COLOUR : Nat)
        (DEPENDENCY : List Formula)
deriving Repr
export Deduction (edge)
/- DLDS: Ancestral Paths -/
structure Ancestral where
path :: (START : Vertex)
        (END : Vertex)
        (COLOURS : List Nat)
deriving Repr
export Ancestral (path)
/- DLDS: Graph -/
structure Graph where
dlds :: (NODES : List Vertex)
        (EDGES : List Deduction)
        (PATHS : List Ancestral)
deriving Repr
export Graph (dlds)
/- DLDS: Neighborhoods -/
structure Neighborhood where
rule :: (CENTER : Vertex)
        (INCOMING : List Deduction)
        (OUTGOING : List Deduction)
        (DIRECT : List Ancestral)
        (INDIRECT : List Ancestral)
deriving Repr
export Neighborhood (rule)

/- Instances of Decidability: Labels -/
@[inline] def Formula.decEq (FORMULA₁ FORMULA₂ : @& Formula) : Decidable (FORMULA₁ = FORMULA₂) :=
match FORMULA₁, FORMULA₂ with
| (atom SBL₁), (atom SBL₂) => by rewrite [Formula.atom.injEq];
                                 exact String.decEq SBL₁ SBL₂;
| (atom _), (implication _ _) => by exact isFalse (Formula.noConfusion);
| (implication _ _), (atom _) => by exact isFalse (Formula.noConfusion);
| (implication ANT₁ CON₁), (implication ANT₂ CON₂) => by
  rewrite [Formula.implication.injEq];
  have DecANT : Decidable (ANT₁ = ANT₂) := Formula.decEq ANT₁ ANT₂;
  have DecCON : Decidable (CON₁ = CON₂) := Formula.decEq CON₁ CON₂;
  exact @instDecidableAnd (ANT₁ = ANT₂) (CON₁ = CON₂) DecANT DecCON;
@[inline] instance : DecidableEq Formula := Formula.decEq
/- Instances of Decidability: Vertices -/
@[inline] def Vertex.decEq (NODE₁ NODE₂ : @& Vertex) : Decidable (NODE₁ = NODE₂) :=
match NODE₁, NODE₂ with
| (node NBR₁ LVL₁ FML₁ HPT₁ COL₁ PST₁), (node NBR₂ LVL₂ FML₂ HPT₂ COL₂ PST₂) => by
  rewrite [Vertex.node.injEq];
  have DecNBR : Decidable (NBR₁ = NBR₂) := Nat.decEq NBR₁ NBR₂;
  have DecLVL : Decidable (LVL₁ = LVL₂) := Nat.decEq LVL₁ LVL₂;
  have DecFML : Decidable (FML₁ = FML₂) := Formula.decEq FML₁ FML₂;
  have DecHPT : Decidable (HPT₁ = HPT₂) := Bool.decEq HPT₁ HPT₂;
  have DecCPS : Decidable (COL₁ = COL₂) := Bool.decEq COL₁ COL₂;
  have DecPST : Decidable (PST₁ = PST₂) := List.hasDecEq PST₁ PST₂;
  have DecAND₁ := @instDecidableAnd (COL₁ = COL₂) (PST₁ = PST₂) DecCPS DecPST;
  have DecAND₂ := @instDecidableAnd (HPT₁ = HPT₂) ( COL₁ = COL₂
                                                  ∧ PST₁ = PST₂ ) DecHPT DecAND₁;
  have DecAND₃ := @instDecidableAnd (FML₁ = FML₂) ( HPT₁ = HPT₂
                                                  ∧ COL₁ = COL₂
                                                  ∧ PST₁ = PST₂ ) DecFML DecAND₂;
  have DecAND₄ := @instDecidableAnd (LVL₁ = LVL₂) ( FML₁ = FML₂
                                                  ∧ HPT₁ = HPT₂
                                                  ∧ COL₁ = COL₂
                                                  ∧ PST₁ = PST₂ ) DecLVL DecAND₃;
  exact @instDecidableAnd (NBR₁ = NBR₂) ( LVL₁ = LVL₂
                                        ∧ FML₁ = FML₂
                                        ∧ HPT₁ = HPT₂
                                        ∧ COL₁ = COL₂
                                        ∧ PST₁ = PST₂ ) DecNBR DecAND₄;
@[inline] instance : DecidableEq Vertex := Vertex.decEq
/- Instances of Decidability: Deduction Edges -/
@[inline] def Deduction.decEq (EDGE₁ EDGE₂ : @& Deduction) : Decidable (EDGE₁ = EDGE₂) :=
match EDGE₁, EDGE₂ with
| (edge STT₁ END₁ CLR₁ DEP₁), (edge STT₂ END₂ CLR₂ DEP₂) => by
  rewrite [Deduction.edge.injEq];
  have DecSTT : Decidable (STT₁ = STT₂) := Vertex.decEq STT₁ STT₂;
  have DecEND : Decidable (END₁ = END₂) := Vertex.decEq END₁ END₂;
  have DecCLR : Decidable (CLR₁ = CLR₂) := Nat.decEq CLR₁ CLR₂;
  have DecDEP : Decidable (DEP₁ = DEP₂) := List.hasDecEq DEP₁ DEP₂;
  have DecAND₁ := @instDecidableAnd (CLR₁ = CLR₂) (DEP₁ = DEP₂) DecCLR DecDEP;
  have DecAND₂ := @instDecidableAnd (END₁ = END₂) (CLR₁ = CLR₂ ∧ DEP₁ = DEP₂) DecEND DecAND₁;
  exact @instDecidableAnd (STT₁ = STT₂) (END₁ = END₂ ∧ CLR₁ = CLR₂ ∧ DEP₁ = DEP₂) DecSTT DecAND₂;
@[inline] instance : DecidableEq Deduction := Deduction.decEq
/- Instances of Decidability: Ancestral Paths -/
@[inline] def Ancestral.decEq (PATH₁ PATH₂ : @& Ancestral) : Decidable (PATH₁ = PATH₂) :=
match PATH₁, PATH₂ with
| (path STT₁ END₁ CLRS₁), (path STT₂ END₂ CLRS₂) => by
  rewrite [Ancestral.path.injEq];
  have DecSTT : Decidable (STT₁ = STT₂) := Vertex.decEq STT₁ STT₂;
  have DecEND : Decidable (END₁ = END₂) := Vertex.decEq END₁ END₂;
  have DecCLRS : Decidable (CLRS₁ = CLRS₂) := List.hasDecEq CLRS₁ CLRS₂;
  have DecAND := @instDecidableAnd (END₁ = END₂) (CLRS₁ = CLRS₂) DecEND DecCLRS;
  exact @instDecidableAnd (STT₁ = STT₂) (END₁ = END₂ ∧ CLRS₁ = CLRS₂) DecSTT DecAND;
@[inline] instance : DecidableEq Ancestral := Ancestral.decEq
/- Instances of Decidability: Graph -/
@[inline] def Graph.decEq (DLDS₁ DLDS₂ : @& Graph) : Decidable (DLDS₁ = DLDS₂) := by
match DLDS₁, DLDS₂ with
| (dlds NODES₁ EDGES₁ PATHS₁), (dlds NODES₂ EDGES₂ PATHS₂) =>
  rewrite [Graph.dlds.injEq];
  have DecNODES : Decidable (NODES₁ = NODES₂) := List.hasDecEq NODES₁ NODES₂;
  have DecEDGES : Decidable (EDGES₁ = EDGES₂) := List.hasDecEq EDGES₁ EDGES₂;
  have DecPATHS : Decidable (PATHS₁ = PATHS₂) := List.hasDecEq PATHS₁ PATHS₂;
  have DecAND := @instDecidableAnd (EDGES₁ = EDGES₂) (PATHS₁ = PATHS₂) DecEDGES DecPATHS;
  exact @instDecidableAnd (NODES₁ = NODES₂) (EDGES₁ = EDGES₂ ∧ PATHS₁ = PATHS₂) DecNODES DecAND;
@[inline] instance : DecidableEq Graph := Graph.decEq
/- Instances of Decidability: Neighborhoods -/
@[inline] def Neighborhood.decEq (RULE₁ RULE₂ : @& Neighborhood) : Decidable (RULE₁ = RULE₂) :=
match RULE₁, RULE₂ with
| (rule CTR₁ INC₁ OUT₁ DIR₁ IND₁), (rule CTR₂ INC₂ OUT₂ DIR₂ IND₂) => by
  rewrite [Neighborhood.rule.injEq];
  have DecCTR : Decidable (CTR₁ = CTR₂) := Vertex.decEq CTR₁ CTR₂;
  have DecINC : Decidable (INC₁ = INC₂) := List.hasDecEq INC₁ INC₂;
  have DecOUT : Decidable (OUT₁ = OUT₂) := List.hasDecEq OUT₁ OUT₂;
  have DecDIR : Decidable (DIR₁ = DIR₂) := List.hasDecEq DIR₁ DIR₂;
  have DecIND : Decidable (IND₁ = IND₂) := List.hasDecEq IND₁ IND₂;
  have DecAND₁ := @instDecidableAnd (DIR₁ = DIR₂) (IND₁ = IND₂) DecDIR DecIND;
  have DecAND₂ := @instDecidableAnd (OUT₁ = OUT₂) ( DIR₁ = DIR₂
                                                  ∧ IND₁ = IND₂ ) DecOUT DecAND₁;
  have DecAND₃ := @instDecidableAnd (INC₁ = INC₂) ( OUT₁ = OUT₂
                                                  ∧ DIR₁ = DIR₂
                                                  ∧ IND₁ = IND₂ ) DecINC DecAND₂;
  exact @instDecidableAnd (CTR₁ = CTR₂) ( INC₁ = INC₂
                                        ∧ OUT₁ = OUT₂
                                        ∧ DIR₁ = DIR₂
                                        ∧ IND₁ = IND₂ ) DecCTR DecAND₃;
@[inline] instance : DecidableEq Neighborhood := Neighborhood.decEq

/- Unfold Equality: Vertex -/
theorem Vertex.node.injEq' {NODE₁ NODE₂ : Vertex} :
  -----------------------------------------------------------------------------------
  ( (NODE₁ = NODE₂) ↔ ( NODE₁.NUMBER = NODE₂.NUMBER
                      ∧ NODE₁.LEVEL = NODE₂.LEVEL
                      ∧ NODE₁.FORMULA = NODE₂.FORMULA
                      ∧ NODE₁.HYPOTHESIS = NODE₂.HYPOTHESIS
                      ∧ NODE₁.COLLAPSED = NODE₂.COLLAPSED
                      ∧ NODE₁.PAST = NODE₂.PAST ) ) := by
match NODE₁, NODE₂ with
| (node NBR₁ LVL₁ FML₁ HPT₁ COL₁ PST₁),
  (node NBR₂ LVL₂ FML₂ HPT₂ COL₂ PST₂) => simp only [Vertex.node.injEq];
/- Unfold Equality: Deduction -/
theorem Deduction.edge.injEq' {EDGE₁ EDGE₂ : Deduction} :
  -----------------------------------------------------------------------------------
  ( (EDGE₁ = EDGE₂) ↔ ( EDGE₁.START = EDGE₂.START
                      ∧ EDGE₁.END = EDGE₂.END
                      ∧ EDGE₁.COLOUR = EDGE₂.COLOUR
                      ∧ EDGE₁.DEPENDENCY = EDGE₂.DEPENDENCY ) ) := by
match EDGE₁, EDGE₂ with
| (edge STT₁ END₁ CLR₁ DEP₁), (edge STT₂ END₂ CLR₂ DEP₂) => simp only [Deduction.edge.injEq];
/- Unfold Equality: Ancestral -/
theorem Ancestral.path.injEq' {PATH₁ PATH₂ : Ancestral} :
  -----------------------------------------------------------------------------------
  ( (PATH₁ = PATH₂) ↔ ( PATH₁.START = PATH₂.START
                      ∧ PATH₁.END = PATH₂.END
                      ∧ PATH₁.COLOURS = PATH₂.COLOURS ) ) := by
match PATH₁, PATH₂ with
| (path STT₁ END₁ CLRS₁), (path STT₂ END₂ CLRS₂) => simp only [Ancestral.path.injEq];

/- Methods & Definitions -/
/- Get: Incoming Deductions -/--------------------------------------------------------------------------------------------------
def get_rule.incoming (NODE : Vertex) (DLDS : Graph) : List Deduction :=
    loop NODE DLDS.EDGES
    where loop (NODE : Vertex) (EDGES : List Deduction) : List Deduction :=
          match EDGES with
          | [] => []
          | (EDGE::EDGES) => if   ( EDGE.END = NODE )
                             then ( EDGE :: loop NODE EDGES )
                             else ( loop NODE EDGES )
    ----------------------------------------------------------------------------------------------------------------------------
/- Get: Outgoing Deductions -/--------------------------------------------------------------------------------------------------
def get_rule.outgoing (NODE : Vertex) (DLDS : Graph) : List Deduction :=
    loop NODE DLDS.EDGES
    where loop (NODE : Vertex) (EDGES : List Deduction) : List Deduction :=
          match EDGES with
          | [] => []
          | (EDGE::EDGES) => if   ( EDGE.START = NODE )
                             then ( EDGE :: loop NODE EDGES )
                             else ( loop NODE EDGES )
    ----------------------------------------------------------------------------------------------------------------------------
/- Get: Direct Ancestrals -/----------------------------------------------------------------------------------------------------
def get_rule.direct (NODE : Vertex) (DLDS : Graph) : List Ancestral :=
    loop NODE DLDS.PATHS
    where loop (NODE : Vertex) (PATHS : List Ancestral) : List Ancestral :=
          match PATHS with
          | [] => []
          | (PATH::PATHS) => if   ( PATH.END = NODE )
                             then ( PATH :: loop NODE PATHS )
                             else ( loop NODE PATHS )
    ----------------------------------------------------------------------------------------------------------------------------
/- Get: Indirect Ancestrals -/--------------------------------------------------------------------------------------------------
def get_rule.indirect (NODE : Vertex) (DLDS : Graph) : List Ancestral :=
    loop (get_rule.incoming NODE DLDS) DLDS.PATHS
    where loop (EDGES : List Deduction) (PATHS : List Ancestral) : List Ancestral :=
          match EDGES with
          | [] => []
          | (EDGE::EDGES) => get_rule.direct.loop EDGE.START PATHS ++ loop EDGES PATHS
    ----------------------------------------------------------------------------------------------------------------------------
/- Collapse: NODE × DLDS → Neighborhood -/--------------------------------------------------------------------------------------
def get_rule (NODE : Vertex) (DLDS : Graph) : Neighborhood :=
    rule ( NODE )
         ( get_rule.incoming NODE DLDS )
         ( get_rule.outgoing NODE DLDS )
         ( get_rule.direct NODE DLDS )
         ( get_rule.indirect NODE DLDS )
    ----------------------------------------------------------------------------------------------------------------------------

/- Collapse & Type Conditionals -/
/- Check: Past Collapses (Vertex) & Path Colours (Ancestral) -/-------------------------------------------------------------
def check_numbers (NUMBERS : List Nat) : Prop :=
    ( NUMBERS ≠ [] )
  ∧ ( ∀{NUMBER : Nat}, ( NUMBER ∈ NUMBERS ) → ( NUMBER > 0 ) )
    ------------------------------------------------------------------------------------------------------------------------
/- Check: Nodes Set (Graph) -/----------------------------------------------------------------------------------------------
def check_dlds (DLDS : Graph) : Prop :=
    ( ∀{NODE₁ NODE₂ : Vertex}, ( NODE₁ ∈ DLDS.NODES ) →
                               ( NODE₂ ∈ DLDS.NODES ) →
      --------------------------------------
      ( ( NODE₁.NUMBER = NODE₂.NUMBER ) ↔ ( NODE₁ = NODE₂ ) ) )
  ∧ ( ∀{EDGE : Deduction}, ( EDGE ∈ DLDS.EDGES ) →
      --------------------------------------
      ( EDGE.START ∈ DLDS.NODES ∧ EDGE.END ∈ DLDS.NODES ) )
  ∧ ( ∀{PATH : Ancestral}, ( PATH ∈ DLDS.PATHS ) →
      --------------------------------------
      ( PATH.START ∈ DLDS.NODES ∧ PATH.END ∈ DLDS.NODES ) )
    ------------------------------------------------------------------------------------------------------------------------
/- Check: Collapse Nodes (Vertexes) & Incoming Edges (Deductions) -/--------------------------------------------------------
def check_collapse_nodes (RULEᵤ RULEᵥ : Neighborhood) : Prop :=
    ( RULEᵤ.CENTER.NUMBER > RULEᵥ.CENTER.NUMBER )
  ∧ ( RULEᵥ.CENTER.NUMBER ∉ RULEᵤ.CENTER.PAST )
  ∧ ( RULEᵤ.CENTER.LEVEL = RULEᵥ.CENTER.LEVEL )
  ∧ ( RULEᵤ.CENTER.FORMULA = RULEᵥ.CENTER.FORMULA )
  ∧ ( ∀{INCᵤ INCᵥ : Deduction}, ( INCᵤ ∈ RULEᵤ.INCOMING ) →
                                ( INCᵥ ∈ RULEᵥ.INCOMING ) →
                                ( INCᵤ.START ≠ INCᵥ.START ) )
    ------------------------------------------------------------------------------------------------------------------------
/- Check: Outgoing Edges (Deductions) & Collapse Nodes (Vertexes) & Incoming Edges (Deductions) -/-------------------------
def check_collapse_edges (RULEᵤ RULEᵥ : Neighborhood) : Prop :=
    ( ∃(OUTᵤ OUTᵥ : Deduction), ( OUTᵤ ∈ RULEᵤ.OUTGOING )
                              ∧ ( OUTᵥ ∈ RULEᵥ.OUTGOING )
                              ∧ ( OUTᵤ.COLOUR > 0 )
                              ∧ ( OUTᵥ.END = OUTᵤ.END )
                              ∧ ( OUTᵥ.COLOUR = OUTᵤ.COLOUR )
                              ∧ ( OUTᵥ.DEPENDENCY = OUTᵤ.DEPENDENCY ) )
  ∧ ( RULEᵤ.CENTER.LEVEL = RULEᵥ.CENTER.LEVEL )
  ∧ ( RULEᵤ.CENTER.FORMULA = RULEᵥ.CENTER.FORMULA )
  ∧ ( ∀{INCᵤ INCᵥ : Deduction}, ( INCᵤ ∈ RULEᵤ.INCOMING ) →
                                ( INCᵥ ∈ RULEᵥ.INCOMING ) →
                                ( INCᵤ.START ≠ INCᵥ.START ) )
    ------------------------------------------------------------------------------------------------------------------------

/- End -/
