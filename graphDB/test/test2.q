(:P {nom string, age int, ville string})
(:E {nom string, pme bool, secteur string})


(:P) -[:ami]-> (:P)
(:P) -[:emp]-> (:E)
(:E) -[:f]-> (:E)
(:P) -[:coloc]-> (:P)

(* Commentaire *)

create
   (marie: P) -[:emp]-> (ab: E),
   (clement: P) -[:emp]-> (ab: E),
   (pierre: P) -[:emp]-> (pp: E),
   (sophie: P) -[:emp]-> (tf: E),
   (luc: P) -[:emp]-> (tf: E),
   (julie: P) -[:emp]-> (sncf: E),
   (antoine: P) -[:emp]-> (sncf: E),
   (emma: P) -[:emp]-> (lcl: E),
   (thomas: P) -[:emp]-> (lcl: E),
   (lea: P) -[:emp]-> (boulangerie: E)
   

set
   marie.nom = "Marie Dubois",    marie.age = 25,   marie.ville = "Toulouse",
   clement.nom = "Clement Roux",  clement.age = 32, clement.ville = "Toulouse",
   pierre.nom = "Pierre Dupont",  pierre.age = 24,  pierre.ville = "Paris",
   sophie.nom = "Sophie Martin",  sophie.age = 28,  sophie.ville = "Lyon",
   luc.nom = "Luc Bernard",       luc.age = 35,     luc.ville = "Lyon",
   julie.nom = "Julie Lefevre",   julie.age = 27,   julie.ville = "Paris",
   antoine.nom = "Antoine Morel", antoine.age = 30, antoine.ville = "Paris",
   emma.nom = "Emma Durand",      emma.age = 23,    emma.ville = "Nantes",
   thomas.nom = "Thomas Petit",   thomas.age = 29,  thomas.ville = "Nantes",
   lea.nom = "Lea Simon",         lea.age = 26,     lea.ville = "Bordeaux",
   ab.nom = "Airbus",             ab.pme = false,    ab.secteur = "Aeronautique",
   pp.nom = "Petit Pain",         pp.pme = true,     pp.secteur = "Boulangerie",
   tf.nom = "Total France",       tf.pme = false,    tf.secteur = "Energie",
   sncf.nom = "SNCF",             sncf.pme = false,  sncf.secteur = "Transport",
   lcl.nom = "LCL",               lcl.pme = false,   lcl.secteur = "Banque",
   boulangerie.nom = "Boulangerie Locale", boulangerie.pme = true, boulangerie.secteur = "Boulangerie"

create
   (pp) -[:f]-> (ab),
   (boulangerie) -[:f]-> (sncf),
   (pp) -[:f]-> (lcl),
   (marie) -[:emp]-> (ab),
   (pierre) -[:emp]-> (pp),
   (sophie) -[:emp]-> (sncf),
   (luc) -[:emp]-> (ab),
   (marie) -[:ami]-> (pierre),
   (clement) -[:ami]-> (pierre),
   (sophie) -[:ami]-> (luc),
   (julie) -[:ami]-> (antoine),
   (emma) -[:ami]-> (thomas),
   (lea) -[:ami]-> (julie),
   (marie) -[:coloc]-> (clement),
   (sophie) -[:coloc]-> (luc),
   (julie) -[:coloc]-> (antoine)



match 
   (p1: P) -[:emp]-> (e: E) -[:f]-> (e2: E),
   (p1) -[:ami]-> (p2: P)

where 
   p1.age < 30 

return 
   p1, p2, e, e2

