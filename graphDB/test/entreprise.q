(:P {nom string, age int})
(:E {nom string, pme bool})

(:P) -[:ami]-> (:P)
(:P) -[:emp]-> (:E)
(:E) -[:f] -> (:E)

create
   (marie: P) -[:emp]-> (ab: E),
   (pierre: P) -[:emp]-> (pp: E)
set
   marie.nom = "Marie Dubois",    marie.age = 25,
   pierre.nom = "Pierre Dupont", pierre.age = 24,
   ab.nom = "Airbus", ab.pme = false,
   pp.nom = "Petit Pain", pp.pme = true
create
   (pp) -[:f]-> (ab),
   (marie) -[:emp]-> (ab),
   (pierre) -[:emp]-> (pp),
   (marie) -[:ami]-> (pierre)

match (p: P) -[:emp]-> (e: E)
where p.age < 25

return p, e
