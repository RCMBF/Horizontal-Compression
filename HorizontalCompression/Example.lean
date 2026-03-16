import HorizontalCompression

/- Example -/
--Lvl.5:
def n0 := ( node 0 5 #"A1" true false [] )
def n1 := ( node 1 5 (#"A1" >> #"A2") true false [] )
def n2 := ( node 2 5 #"A1" true false [] )
def n3 := ( node 3 5 (#"A1" >> (#"A2" >> #"A3")) true false [] )
def n4 := ( node 4 5 #"A1" true false [] )
def n5 := ( node 5 5 (#"A1" >> #"A2") true false [] )
def n6 := ( node 6 5 #"A1" true false [] )
def n7 := ( node 7 5 (#"A1" >> #"A2") true false [] )
def n8 := ( node 8 5 #"A1" true false [] )
def n9 := ( node 9 5 (#"A1" >> (#"A2" >> #"A3")) true false [] )
--Lvl.4:
def n10 := ( node 10 4 #"A2" false false [] )
def n11 := ( node 11 4 (#"A2" >> #"A3") false false [] )
def n12 := ( node 12 4 #"A2" false false [] )
def n13 := ( node 13 4 (#"A2" >> (#"A3" >> #"A4")) true false [] )
def n14 := ( node 14 4 #"A2" false false [] )
def n15 := ( node 15 4 (#"A2" >> #"A3") false false [] )
--Lvl.3:
def n16 := ( node 16 3 #"A3" false false [] )
def n17 := ( node 17 3 (#"A3" >> #"A4") false false [] )
def n18 := ( node 18 3 #"A3" false false [] )
def n19 := ( node 19 3 (#"A3" >> (#"A4" >> #"A5")) true false [] )
--Lvl.2:
def n20 := ( node 20 2 #"A4" false false [] )
def n21 := ( node 21 2 (#"A4" >> #"A5") false false [] )
--Lvl.1:
def n22 := ( node 22 1 #"A5" false false [] )
--Lvl.0:
def n23 := ( node 23 0 (#"A4" >> #"A5") false false [] )
-------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------
def e0 := ( edge (n0) (n10) 0 [#"A1"] )
def e1 := ( edge (n1) (n10) 0 [(#"A1" >> #"A2")] )
def e2 := ( edge (n2) (n11) 0 [#"A1"] )
def e3 := ( edge (n3) (n11) 0 [(#"A1" >> (#"A2" >> #"A3"))] )
def e4 := ( edge (n4) (n12) 0 [#"A1"] )
def e5 := ( edge (n5) (n12) 0 [(#"A1" >> #"A2")] )
def e6 := ( edge (n6) (n14) 0 [#"A1"] )
def e7 := ( edge (n7) (n14) 0 [(#"A1" >> #"A2")] )
def e8 := ( edge (n8) (n15) 0 [#"A1"] )
def e9 := ( edge (n9) (n15) 0 [(#"A1" >> (#"A2" >> #"A3"))] )
-------------------------------------------------------------------------------------------------------------------------------
def e10 := ( edge (n10) (n16) 0 [#"A1", (#"A1" >> #"A2")] )
def e11 := ( edge (n11) (n16) 0 [#"A1", (#"A1" >> (#"A2" >> #"A3"))] )
def e12 := ( edge (n12) (n17) 0 [#"A1", (#"A1" >> #"A2")] )
def e13 := ( edge (n13) (n17) 0 [(#"A2" >> (#"A3" >> #"A4"))] )
def e14 := ( edge (n14) (n18) 0 [#"A1", (#"A1" >> #"A2")] )
def e15 := ( edge (n15) (n18) 0 [#"A1", (#"A1" >> (#"A2" >> #"A3"))] )
-------------------------------------------------------------------------------------------------------------------------------
def e16 := ( edge (n16) (n20) 0 [#"A1", (#"A1" >> #"A2")] )
def e17 := ( edge (n17) (n20) 0 [#"A1", (#"A1" >> (#"A2" >> #"A3"))] )
def e18 := ( edge (n18) (n21) 0 [#"A1", (#"A1" >> #"A2"), (#"A1" >> (#"A2" >> #"A3"))] )
def e19 := ( edge (n19) (n21) 0 [(#"A3" >> (#"A4" >> #"A5"))] )
-------------------------------------------------------------------------------------------------------------------------------
def e20 := ( edge (n20) (n22) 0 [#"A1", (#"A1" >> #"A2"), (#"A1" >> (#"A2" >> #"A3"))] )
def e21 := ( edge (n21) (n22) 0 [#"A1", (#"A1" >> #"A2"), (#"A1" >> (#"A2" >> #"A3")), (#"A3" >> (#"A4" >> #"A5"))] )
-------------------------------------------------------------------------------------------------------------------------------
def e22 := ( edge (n22) (n23) 0 [#"A1", (#"A1" >> #"A2"), (#"A1" >> (#"A2" >> #"A3")), (#"A3" >> (#"A4" >> #"A5"))] )
-------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------
def d0 := ( dlds [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23]
                 [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22]
                 [] )

/- Test -/
#eval d0
#eval get_levels d0
#eval get_labels d0
#eval repeated_nodes_string d0

-- Lvl. 3: Nodes 16 & 18
def d1 := collapse_nodes_nat 16 18 d0
#eval repeated_nodes_string d1

-- Lvl. 4: Nodes 11 & 15
def d2 := collapse_nodes_nat 11 15 d1
#eval repeated_nodes_string d2

-- Lvl. 4: Nodes 10 & 12
def d3 := collapse_nodes_nat 10 12 d2
#eval repeated_nodes_string d3

-- Lvl. 4: Nodes 10 & 14
def d4 := collapse_nodes_nat 10 14 d3
#eval repeated_nodes_string d4

-- Lvl. 5: Nodes 3 & 9
def d5 := collapse_nodes_nat 3 9 d4
#eval repeated_nodes_string d5

-- Lvl. 5: Nodes 1 & 5
def d6 := collapse_nodes_nat 1 5 d5
#eval repeated_nodes_string d6

-- Lvl. 5: Nodes 1 & 7
def d7 := collapse_nodes_nat 1 7 d6
#eval repeated_nodes_string d7

-- Lvl. 5: Nodes 0 & 2
def d8 := collapse_nodes_nat 0 2 d7
#eval repeated_nodes_string d8

-- Lvl. 5: Nodes 0 & 4
def d9 := collapse_nodes_nat 0 4 d8
#eval repeated_nodes_string d9

-- Lvl. 5: Nodes 0 & 6
def d10 := collapse_nodes_nat 0 6 d9
#eval repeated_nodes_string d10

-- Lvl. 5: Nodes 0 & 8
def d11 := collapse_nodes_nat 0 8 d10
#eval repeated_nodes_string d11
#eval d11

-- Result of HC:
def d11' := compress_nodes_graph d0
#eval repeated_nodes_string d11'
#eval d11'

-- Checks:
#eval check_sub_graph d11 d11'
#eval check_sub_graph d11' d11
#eval d11 = d11'

/- End -/
