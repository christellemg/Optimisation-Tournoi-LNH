/*********************************************
 * OPL 20.1.0.0 Model
 * Author: 15142
 * Creation Date: 30 avr. 2021 at 16 h 05 min 31 s
 *********************************************/
 
 
using CP;

range Teams=1..6;
int N_i = ...;
range I = 1..N_i;
range S = 1..(N_i+1);
setof(string) Home=...; 
float Distance[Teams][Teams]= ...;


//Variable décision 

dvar int Ville_precedente_Mtl[S];
dvar int Ville_precedente_Tor[S];
dvar int Ville_precedente_Ott[S];
dvar int Ville_precedente_Win[S];
dvar int Ville_precedente_Cal[S];
dvar int Ville_precedente_Edm[S];


dvar boolean Mtl[I][Teams][Home]; 
dvar boolean Tor[I][Teams][Home];  
dvar boolean Ott[I][Teams][Home];
dvar boolean Win[I][Teams][Home];
dvar boolean Cal[I][Teams][Home];
dvar boolean Edm[I][Teams][Home];

//Fonction obj 

minimize sum(test in 2..N_i+1) (Distance[Ville_precedente_Mtl[test-1]][Ville_precedente_Mtl[test]]) + Distance[Ville_precedente_Mtl[N_i+1]][1] +                                       
		 sum(test in 2..N_i+1) (Distance[Ville_precedente_Tor[test-1]][Ville_precedente_Tor[test]]) + Distance[Ville_precedente_Tor[N_i+1]][2] +
		 sum(test in 2..N_i+1) (Distance[Ville_precedente_Ott[test-1]][Ville_precedente_Ott[test]]) + Distance[Ville_precedente_Ott[N_i+1]][3] +
		 sum(test in 2..N_i+1) (Distance[Ville_precedente_Win[test-1]][Ville_precedente_Win[test]]) + Distance[Ville_precedente_Win[N_i+1]][4] +
		 sum(test in 2..N_i+1) (Distance[Ville_precedente_Cal[test-1]][Ville_precedente_Cal[test]]) + Distance[Ville_precedente_Cal[N_i+1]][5] +
		 sum(test in 2..N_i+1) (Distance[Ville_precedente_Edm[test-1]][Ville_precedente_Edm[test]]) + Distance[Ville_precedente_Edm[N_i+1]][6];



//Contrainte 

subject to {
 // MONTREAL     
// Contrainte liante de ville précédente 

	//Mtl commence part de montreal même si son premier match est ailleurs! 
	Ville_precedente_Mtl[1] == 1;
	
	//Si une équipe à jouer son match précédent à l'extéreur alors elle arrive de labas
	forall(i in 2..N_i+1, j in Teams) (Mtl[i-1][j]["0"]==1) => (Ville_precedente_Mtl[i] == j);
 	
 	//Si Mtl joue son match précédent à la maison alors elle arrive de Mtl
    forall(i in 2..N_i+1, j in Teams) (Mtl[i-1][j]["1"]==1) => (Ville_precedente_Mtl[i] == 1);
	  
	  
// Mtl ne joue pas contre lui-même 
forall(i in 1..N_i, k in Home) Mtl[i][1][k]==0 ; 

// Mtl joue 1 fois a domicile contre chaque équipe et 1 fois a l'exterieur contre chaque équipe
forall(Teams in 2..6, k in Home) sum(i in I) Mtl[i][Teams][k]==1;

// Mtl joue un match à la fois
forall(i in I) sum(j in Teams, k in Home) Mtl[i][j][k]==1 ;

// Mtl joue maximum 3 matchs à l'exterieur de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Mtl[i+z][j]["0"]) <= 3 ;

// Mtl joue maximum 3 matchs à domicile de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Mtl[i+z][j]["1"]) <= 3 ;



//TORONTO
// Contrainte liante de ville précédente 

	//Tor part de Tor même si son premier match est ailleurs! 
	Ville_precedente_Tor[1] == 2;
	
	//Si une équipe à jouer son match précédent à l'extéreur alors elle arrive de labas
	forall(i in 2..N_i+1, j in Teams) (Tor[i-1][j]["0"]==1) => (Ville_precedente_Tor[i] == j);
 	
 	//Si Tor joue son match précédent à la maison alors elle arrive de Tor
    forall(i in 2..N_i+1, j in Teams) (Tor[i-1][j]["1"]==1) => (Ville_precedente_Tor[i] == 2);
    
    
// Tor ne joue pas contre lui-même 
forall(i in 1..N_i, k in Home) Tor[i][2][k]==0 ; 

// Tor joue 1 fois a domicile contre chaque équipe et 1 fois a l'exterieur contre chaque équipe
forall(Teams in {1,3,4,5,6}, k in Home) sum(i in I) Tor[i][Teams][k]==1;

// Tor joue un match à la fois
forall(i in I) sum(j in Teams, k in Home) Tor[i][j][k]==1 ;

// Tor joue maximum 3 matchs à l'exterieur de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Tor[i+z][j]["0"]) <= 3 ;

// Tor joue maximum 3 matchs à domicile de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Tor[i+z][j]["1"]) <= 3 ;

//Ottawa
// Contrainte liante de ville précédente 

	//Ott  part de ott même si son premier match est ailleurs! 
	Ville_precedente_Ott[1] == 3;
	
	//Si une équipe à jouer son match précédent à l'extéreur alors elle arrive de labas
	forall(i in 2..N_i+1, j in Teams) (Ott[i-1][j]["0"]==1) => (Ville_precedente_Ott[i] == j);
 	
 	//Si Ott joue son match précédent à la maison alors elle arrive de Ott
    forall(i in 2..N_i+1, j in Teams) (Ott[i-1][j]["1"]==1) => (Ville_precedente_Ott[i] == 3);

// Ott ne joue pas contre lui-même 
forall(i in 1..N_i, k in Home) Ott[i][3][k]==0 ; 

// Ott joue 1 fois a domicile contre chaque équipe et 1 fois a l'exterieur contre chaque équipe
forall(Teams in {1,2,4,5,6}, k in Home) sum(i in I) Ott[i][Teams][k]==1;

// Ott joue un match à la fois
forall(i in I) sum(j in Teams, k in Home) Ott[i][j][k]==1 ;

// Ott joue maximum 3 matchs à l'exterieur de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Ott[i+z][j]["0"]) <= 3 ;

// Ott joue maximum 3 matchs à domicile de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Ott[i+z][j]["1"]) <= 3 ;



//Winnipeg
// Contrainte liante de ville précédente 

	//Win commence part de Winnipeg même si son premier match est ailleurs! 
	Ville_precedente_Win[1] == 4;
	
	//Si une équipe à jouer son match précédent à l'extéreur alors elle arrive de labas
	forall(i in 2..N_i+1, j in Teams) (Win[i-1][j]["0"]==1) => (Ville_precedente_Win[i] == j);
 	
 	//Si Win joue son match précédent à la maison alors elle arrive de Ott
    forall(i in 2..N_i+1, j in Teams) (Win[i-1][j]["1"]==1) => (Ville_precedente_Win[i] == 4);
    

// Win ne joue pas contre lui-même 
forall(i in 1..N_i, k in Home) Win[i][4][k]==0 ; 

// Win joue 1 fois a domicile contre chaque équipe et 1 fois a l'exterieur contre chaque équipe
forall(Teams in {1,2,3,5,6}, k in Home) sum(i in I) Win[i][Teams][k]==1;

// Win joue un match à la fois
forall(i in I) sum(j in Teams, k in Home) Win[i][j][k]==1 ;

// Win joue maximum 3 matchs à l'exterieur de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Win[i+z][j]["0"]) <= 3 ;

// Win joue maximum 3 matchs à domicile de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Win[i+z][j]["1"]) <= 3 ;

//Calgary
// Contrainte liante de ville précédente 

	//Cal commence part de Calgary même son premier match est ailleurs! 
	Ville_precedente_Cal[1] == 5;
	
	//Si une équipe à jouer son match précédent à l'extéreur alors elle arrive de labas
	forall(i in 2..N_i+1, j in Teams) (Cal[i-1][j]["0"]==1) => (Ville_precedente_Cal[i] == j);
 	
 	//Si un équipe joue son match précédent à la maison alors elle arrive de la maison
    forall(i in 2..N_i+1, j in Teams) (Cal[i-1][j]["1"]==1) => (Ville_precedente_Cal[i] == 5);
    

// Cal ne joue pas contre lui-même 
forall(i in 1..N_i, k in Home) Cal[i][5][k]==0 ; 

// Cal joue 1 fois a domicile contre chaque équipe et 1 fois a l'exterieur contre chaque équipe
forall(Teams in {1,2,3,4,6}, k in Home) sum(i in I) Cal[i][Teams][k]==1;

// Cal joue un match à la fois
forall(i in I) sum(j in Teams, k in Home) Cal[i][j][k]==1 ;

// Cal joue maximum 3 matchs à l'exterieur de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Cal[i+z][j]["0"]) <= 3 ;

// Cal joue maximum 3 matchs à domicile de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Cal[i+z][j]["1"]) <= 3 ;

//Edmonton
// Contrainte liante de ville précédente 

	//Edm commence part de Edmonton même son premier match est ailleurs! 
	Ville_precedente_Edm[1] == 6;
	
	//Si une équipe à jouer son match précédent à l'extéreur alors elle arrive de labas
	forall(i in 2..N_i+1, j in Teams) (Edm[i-1][j]["0"]==1) => (Ville_precedente_Edm[i] == j);
 	
 	//Si un équipe joue son match précédent à la maison alors elle arrive de la maison
    forall(i in 2..N_i+1, j in Teams) (Edm[i-1][j]["1"]==1) => (Ville_precedente_Edm[i] == 6);

// Edm ne joue pas contre lui-même 
forall(i in 1..N_i, k in Home) Edm[i][6][k]==0 ; 

// Edm joue 1 fois a domicile contre chaque équipe et 1 fois a l'exterieur contre chaque équipe
forall(Teams in {1,2,3,4,5}, k in Home) sum(i in I) Edm[i][Teams][k]==1;


// Edm joue un match à la fois
forall(i in I) sum(j in Teams, k in Home) Edm[i][j][k]==1 ;

// Edm joue maximum 3 matchs à l'exterieur de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Edm[i+z][j]["0"]) <= 3 ;

// Edm joue maximum 3 matchs à domicile de suite
forall (i in 1..(N_i-3)) sum (z in 0..3, j in Teams) (Edm[i+z][j]["1"]) <= 3 ;

// Contraintes qui lient les équipes

forall(i in I) Mtl[i][2]["0"] == Tor[i][1]["1"];
forall(i in I) Mtl[i][2]["1"] == Tor[i][1]["0"];
forall(i in I) Mtl[i][3]["0"] == Ott[i][1]["1"];
forall(i in I) Mtl[i][3]["1"] == Ott[i][1]["0"];
forall(i in I) Mtl[i][4]["0"] == Win[i][1]["1"];
forall(i in I) Mtl[i][4]["1"] == Win[i][1]["0"];
forall(i in I) Mtl[i][5]["0"] == Cal[i][1]["1"];
forall(i in I) Mtl[i][5]["1"] == Cal[i][1]["0"];
forall(i in I) Mtl[i][6]["0"] == Edm[i][1]["1"];
forall(i in I) Mtl[i][6]["1"] == Edm[i][1]["0"];

forall(i in I) Tor[i][3]["0"] == Ott[i][2]["1"];
forall(i in I) Tor[i][3]["1"] == Ott[i][2]["0"];
forall(i in I) Tor[i][4]["0"] == Win[i][2]["1"];
forall(i in I) Tor[i][4]["1"] == Win[i][2]["0"];
forall(i in I) Tor[i][5]["0"] == Cal[i][2]["1"];
forall(i in I) Tor[i][5]["1"] == Cal[i][2]["0"];
forall(i in I) Tor[i][6]["0"] == Edm[i][2]["1"];
forall(i in I) Tor[i][6]["1"] == Edm[i][2]["0"];

forall(i in I) Ott[i][4]["0"] == Win[i][3]["1"];
forall(i in I) Ott[i][4]["1"] == Win[i][3]["0"];
forall(i in I) Ott[i][5]["0"] == Cal[i][3]["1"];
forall(i in I) Ott[i][5]["1"] == Cal[i][3]["0"];
forall(i in I) Ott[i][6]["0"] == Edm[i][3]["1"];
forall(i in I) Ott[i][6]["1"] == Edm[i][3]["0"];

forall(i in I) Win[i][5]["0"] == Cal[i][4]["1"];
forall(i in I) Win[i][5]["1"] == Cal[i][4]["0"];
forall(i in I) Win[i][6]["0"] == Edm[i][4]["1"];
forall(i in I) Win[i][6]["1"] == Edm[i][4]["0"];

forall(i in I) Cal[i][6]["0"] == Edm[i][5]["1"];
forall(i in I) Cal[i][6]["1"] == Edm[i][5]["0"];



}





