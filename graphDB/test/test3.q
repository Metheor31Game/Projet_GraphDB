
(:P {nom string, age int, ville string})
(:E {nom string, pme bool, secteur string})

(:P) -[:ami]-> (:P)
(:P) -[:emp]-> (:E)
(:E) -[:f]-> (:E)
(:P) -[:coloc]-> (:P)

create
(marie: P) -[:emp]-> (ab: E)
set
marie.nom = "Marie", marie.age = 12, marie.ville = "Toulouse",
ab.nom = "Airbus", ab.pme = false, ab.secteur = "Aeronotique"

create    
(marie) -[:emp]-> (ab)