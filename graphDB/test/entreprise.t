  $ dune exec Code_GraphDB f entreprise.q
  (Graphstruct.DBG (
     [(Graphstruct.DBN (3,
         ("E",
          [("pme", (Lang.BoolV true)); ("nom", (Lang.StringV "Petit Pain"))])
         ));
       (Graphstruct.DBN (2,
          ("P",
           [("age", (Lang.IntV 24)); ("nom", (Lang.StringV "Pierre Dupont"))])
          ));
       (Graphstruct.DBN (1,
          ("E", [("pme", (Lang.BoolV false)); ("nom", (Lang.StringV "Airbus"))])
          ));
       (Graphstruct.DBN (0,
          ("P",
           [("age", (Lang.IntV 25)); ("nom", (Lang.StringV "Marie Dubois"))])
          ))
       ],
     [(Graphstruct.DBR (0, "ami", 2)); (Graphstruct.DBR (3, "f", 1));
       (Graphstruct.DBR (2, "emp", 3)); (Graphstruct.DBR (0, "emp", 1))]
     ))
  (Sem.Table (["p"; "e"], [[2; 3]]))
