:-  op( 300, xfx, <==).

pos( dziadek(wojtek,  kuba) ).
pos( dziadek(sergiusz,  kuba) ).
pos( dziadek(sergiusz,  mateusz) ).
pos( dziadek(wojtek,  mateusz) ).

neg( dziadek(kuba,  piotr) ).
neg( dziadek(wojtek,  piotr) ).
neg( dziadek(mateusz, kuba) ).
neg( dziadek(wojtek,  magda) ).
neg( dziadek(magda, wojtek) ).
neg( dziadek(wojtek, piotr) ).
neg( dziadek(magda, piotr) ).
neg( dziadek(sergiusz, ola) ).
neg( dziadek(marysia, ola) ).

op( ojciec(piotr, kuba) ).
op( matka(ola, kuba) ).
op( ojciec(piotr, mateusz) ).
op( matka(ola, mateusz) ). 	
op( ojciec(wojtek, piotr) ).
op( matka(magda, piotr) ).
op( ojciec(sergiusz, ola) ).
op( matka(marysia, ola) ).

learn( Class ) :-
   collect_samples(X, collect_positive( Class, X ), Positives, collect_negative( Class, X ), Negatives ),
   learn( Positives, Negatives, Class, Description ),
   writelist( Description ),
   assert( Class  <==  Description).                                      % Assert rule
   
learn( [], _, _, [] ).
learn( Positives, Negatives, Class, [ Rule | RestRules ] ) :-
   initial_rule( Class, InitialRule ),
   learn_conj( Positives, Negatives, InitialRule, Rule ),  % dziadek(rul_var(1),rul_var(2))
   delete_ok( Positives, Rule, RestPositives ),
   learn( RestPositives, Negatives, Class, RestRules ).

%--------------------------------------------------------------%
%
%          Funkcja odpowiedzialna za zebranie przykladow:
%          do Example_Pos: pozytywne
%          do Example_Neg: negatywne
%
%--------------------------------------------------------------% 
collect_samples(X, collect_positive( Class, X ), Positives, collect_negative( Class, X ), Negatives ) :-
   bagof( X, collect_positive( Class, X ), Positives ),            
   bagof( X, collect_negative( Class, X ), Negatives ).  
   
learn_conj( _, [], Rule, Rule ).

learn_conj( Positives, Negatives, RuleIn, RuleOut )  :-
   choose_rule( Positives, Negatives, RuleIn, Rule_Ant ),
  % nl, write('Rule ant: '),write(Rule_Ant),
   delete_not_ok( Negatives, Rule_Ant, RestNegatives ),
   learn_conj( Positives, RestNegatives, Rule_Ant, RuleOut ).
   
%--------------------------------------------------------------
%
%          Nowa funkcja: choose_rule (zamiast choose_cond)
%
%-------------------------------------------------------------- 
choose_rule( Positives, Negatives, RuleIn, RuleOut )  :-
   findall( Rule_Ant / Score, score( Positives, Negatives, RuleIn, Rule_Ant, Score), Rules),
   %nl,write('przed bestem RuleIn: '),write(RuleIn),
   best( Rules, RuleOut )
   %,write('po Bescie RuleOut: '), write(RuleOut ),nl
   .
   
%--------------------------------------------------------------%
%
%          Best zostaje ten sam
%
%--------------------------------------------------------------%  
best( [ AttVal/_], AttVal).

best( [ AV0/S0, AV1/S1 | AVSlist], AttVal)  :-
   S1  >  S0, !,
   best( [AV1/S1 | AVSlist], AttVal)
   ;
   best( [AV0/S0 | AVSlist], AttVal).
   
%--------------------------------------------------------------%
%
%         Zmiany w porownaniu z pierwowzorem:
%          - przyk³ady negatywne nie s¹ dope³nieniem zbioru przyk³adów pozytywnych
%          - NegCount: sprawdzamy czy regula odrzucila conajmniej jednego negatywa
%          - dlatego inaczej liczymy score
%
%--------------------------------------------------------------%    
score( Positives, Negatives, RuleIn, RuleOut, Score ) :-
    length( Negatives, NegCount ),
	%nl, write( 'NegCount: '),write( NegCount),
    candidate( RuleIn, RuleOut ),
    count_ok( Positives, RuleOut, CountPos ),
    count_ok( Negatives, RuleOut, CountNeg ),
    CountPos > 0,
    CountNeg < NegCount,
    Score is CountPos - CountNeg.

%--------------------------------------------------------------%
%
%          - obliczamy aktualna liczbe zmiennych w regule(g)
%          - znajdujemy wszystkie relacje i wrzucamy do listy
%          - wybieramy niedeterministycznie predykaty i zwracamy kandydatow
%         - tworzymy predykaty z nazw i z argumentow
% 
%--------------------------------------------------------------%   	
candidate( rule( P, Q ), rule( P, [ Result | Q ] ) ) :-
  % nl, write( 'Candidate: '),
  % write( 'Q: '),write( Q),write( 'P:'),write( P),nl,
   get_max_number_of_var( rule( P, Q ), CurrentVarNumber ),
   collect_relations( Operatives ),
   member( predicat( Name, 2 ), Operatives ), % wyciaga niedeterministycznie wszystkie name'y(ojciec,matka)
   generate_variables(CurrentVarNumber, Args ),
  % nl, write( 'Wyg(NAme, E,Args): '),write(' '), write( Name),write(' '), write( CurrentVarNumber ),write(' '), write( Args),write('{'), 
   new_pred( Name, Args, Result )
  % ,nl, write( 'Znaleziony kandydat: '),write( Result)
   .

%--------------------------------------------------------------%  
% 
%          Sprawdza, czy dla danego przykladu mozna odnalezc odpowiednie przypisania zmiennych w danej regule.
%          - Ex	: exaple, ktory sprawdzamy
%          - Prev: poprzednik reguly
%          - Next: nastepniki reguly
% 
%--------------------------------------------------------------% 

satisfy( Example, rule( Prev, Next ) ) :-
    Example =.. [ Name | ValuesOfPrev ],
    Prev =.. [ Name | NamesOfPrev ],
    match_variables( NamesOfPrev, ValuesOfPrev, [], Bindings ),
    match_prev_values( Next, Bindings ).

    
%--------------------------------------------------------------% 
% 
%          Sprawdzenie dopasowania ze zmiennymi poprzednika badanaje aktualnie reguly
%           - Prev: lista poprzednikow
%          - Bindings: przypisania zmiennych ustalone wczesniej
% 
%--------------------------------------------------------------% 

match_prev_values( [], Bindings).
match_prev_values( [ Prev | R ], Bindings ) :-  
  %write('matchPre: '),write(Prev),nl,
  %write('B: '),write(Bindings ),nl,
    Prev =.. [ Name | NamesVariables ],
    op( OpFact ),
    OpFact =.. [ Name | ValuesVariables ], 
    match_variables( NamesVariables, ValuesVariables, Bindings, Tmp ),
    match_prev_values( R, Tmp ).

    
%--------------------------------------------------------------% 
%           Sprawdza zgodnosc zmiennych z przypisaniami i ewentualnie uzupelnia przypisania.
%             -NamesVariables: struktury imion
%           - ValuesVariables: - lista zmiennych 
%            - InB: - powi¹zania zmiennych do imion
%--------------------------------------------------------------% 

match_variables( [], [], Bindings, Bindings ).
match_variables( [ ValueVariable | RestNames ], [ ValuesVariable | RestValues ], InB, OutB ) :- 
    member( binding( ValueVariable, ValuesVariable ), InB ),
    match_variables( RestNames, RestValues, InB, OutB ).
match_variables( [ ValueVariable | RestNames ], [ ValuesVariable | RestValues ], InB, OutB ) :- 
    not( member( binding( ValueVariable, _ ), InB ) ),
    match_variables( RestNames, RestValues, [ binding( ValueVariable, ValuesVariable ) | InB ], OutB ).

%--------------------------------------------------------------% 
%
%           Usuniêcie pasujacych przyk³adów operacyjnych
%           Zwraca liste z nieusunietymi pasujacymi
%            
%--------------------------------------------------------------%    
   
delete_ok( [], _, [] ).
delete_ok( [ Example | RestExamples ], Rule, Result )  :-
nl,write('  Remove2'),
   satisfy( Example, Rule ), !,
   delete_ok( RestExamples, Rule, Result ).
delete_ok( [E | RestExamples], Rule, [ E | RestResult ] )  :-
nl,write('  Remove_ SAT_3'),
   delete_ok( RestExamples, Rule, RestResult ).

delete_not_ok( [], _, [] ).
delete_not_ok( [ Example | RestExamples ], Rule, Result )  :-
nl,write('  Remove_ NOT_2 '),write(Example),
   not( satisfy( Example, Rule ) ), !,
   delete_not_ok( RestExamples, Rule, Result ).
delete_not_ok( [E | RestExamples], Rule, [ E | RestResult ] )  :-
nl,write('  Remove_ NOT_3 '),write(Example),
   delete_not_ok( RestExamples, Rule, RestResult ).

%--------------------------------------------------------------% 
%
%          Wykorzystywane przy score
%		   Sprawdza czy spe³nia satisfy() 
%			i zwieksza licznik
%            
%--------------------------------------------------------------%   
   
count_ok( [], _, 0 ).
count_ok( [ Example | RestExamples ], Rule, Result ) :-
    satisfy( Example, Rule ), !,
    count_ok( RestExamples, Rule, Temp ),
    Result is 1 + Temp.
count_ok( [ _ | RestExamples ], Rule, Result ) :-
    count_ok( RestExamples, Rule, Result ).
   
%--------------------------------------------------------------% 
%
%          Utworzenie predykatu za pomoca wyroznika i argumentow
% 			Utworzenie (Dziadek, X1, X2) ->  Dziadek, (X1, X2)
% 			Przypisanie: Result  Dziadek, (X1, X2)    
%       
%--------------------------------------------------------------%   

new_pred( Name, Args, Result ) :-
    Result =.. [ Name | Args ].

%--------------------------------------------------------------% 
%
%          Generacja kolejnych licz oznaczajacych indeksy zmiennych I
%			I = 1,....
%			A1,A2.... 
%       
%--------------------------------------------------------------%   
   
generate_initial_variables( Result ) :-
    generate_initial_variables( 1,  Result ).
generate_initial_variables( I,  [] ) :-
    I > 2, !.    
generate_initial_variables( I,  [ rule_var( I ) | R ] ) :-
%nl,write('rulevar(1)'),write(rule_var( I ) ),nl,
    Ii is I + 1,
    generate_initial_variables( Ii,  R ).

%--------------------------------------------------------------% 	
%
%           Tu przeszukujemy wszystkie pozytywne i znajdujemy te, ktorych klasa pasuje
%           np wszystkie pos(dziadek....) po to aby utworzyc poczatek nastepnika
%
%--------------------------------------------------------------% 	
    	
	
initial_rule( Class, rule( P, [] ) ) :- 
%nl,write('poczatek'),nl,
    bagof( X, collect_positive( Class, X ), [ Example | _ ] ),
	%nl,write('konec'),nl,
	%nl,write('INITIAL argCount'),write(' '),write(ArgCount),write(' P'),write(P), nl,
    generate_initial_variables( InitialVars ),
    new_pred( Class, InitialVars, P )
	.
   
%--------------------------------------------------------------% 	
%
%		Generacja kolejnych liczb naturalnych
%        -N: maks R
%        -R - result
%--------------------------------------------------------------% 	


new_int_generete( N, N ) :- 
    N > 0.
new_int_generete( N, R ) :- 
    N > 0,
    M is N - 1,
    new_int_generete( M, R ).

    
% generate_variables(E, R )
%    Procedura niedeterministyczna, wszystkie mozliwe kombinacje N zmiennych. Indeksy zmiennych moga nalezec 
%     do zbioru [1, N + E - 1], ale kazdy indeks I > E musi miec wartosc N + 1 lub musi istniec element
%   o indeksie I - 1. 
%       N - liczba zmiennych do wygenerowania
%       E - liczba zmiennych z innych poprzednikow i nastepnika
%        R - wynik

%--------------------------------------------------------------% 	
%
%		Generacja kombinacji wszystkich mozliwych N -ek zmiennych
% 		Indeksy generowane sa ze zbioru [1, N - 1 + E]
%
%         - N: liczba zmiennych do wygenerowania
%         - E: liczba zmiennych z innych poprzednikow i nastepnika
%         - A: maksymalna liczba nowych zmiennych
%         - I: numer nastepnej mozliwej nowej zmiennej
%         - R: wynik
%	
%       Nie mo¿e byæ pary x,x+2 jesli wczesniej nie ma x+1.
%
%
%      
%--------------------------------------------------------------% 	


generate_variables(E, R ) :-
    A is E + 1,
    generate_variables(2, E, A, 1, R). 

generate_variables( 0, _, _, _, [] ).
generate_variables( N, E, A, I, [rule_var(RI) | RR] ) :-

    N > 0,
    EA is E + I - 1,
    M is N - 1,
	%write('generate(N E A I): '),write(N),write(' '),write(E),write(' '),write(A),write(' '),write(I),
    new_int_generete( EA, RI ),
    generate_variables( M, E, A, I, RR ).
generate_variables( N, E, A, I, [rule_var(RI) | RR] ) :-
    N > 0, 
    I =< A,
    RI is I + E,
    M is N - 1,
    J is I + 1,
    generate_variables( M, E, A, J, RR ).
   
%--------------------------------------------------------------% 
%
% Obliczanie ilosc zmiennych w dotychczas powstalej regule
% na podstawie liczby zmiennych w poprzedniku i nastepniku
%
%--------------------------------------------------------------% 

%wybiera maksymalny numer
get_max_number_of_var( rule( P, Q ), Result ) :- 
    get_max_number_of_next( P, A ),
    get_max_number_of_ant( Q, B ),
    max( A, B, Result ).

get_max_number_of_ant( [], 0 ).
get_max_number_of_ant( [ Ant | Rest ], Result ) :-
    get_max_number_of_next( Ant, A ), %wybiera maksymalny z nastepnika
    get_max_number_of_ant( Rest, B ), %wybiera maksymalny z poprzednika
    max( A, B, Result ).
    
get_max_number_of_next( P, Result ) :-
    P =.. [ _ | Vars ],
    get_max_from_args( Vars, Result ).

get_max_from_args( [], 0 ).

%wybiera maksymalny z argumentow
get_max_from_args( [ rule_var( X ) | Rest], Result ) :-
    get_max_from_args( Rest, Temp ),
    max( X, Temp, Result ).
 
 
collect_positive( Class, Result ) :-
    pos( Result ),
	% wrzuca do Result nazwe klasy np dziadek
%nl, write( 'Class: ' ), write( Class ),
    Result =.. [ Class | _ ]
%,nl, write( 'collect_positive: zbieraj pozytywa' ),write( 'Result ' ),write( Result ),write( 'Class ' ),write( Class )
.
    
collect_negative( Class, Result ) :-
%nl, write( 'collect_negative: zbieraj negatywa' ),
    neg( Result ),
    Result =.. [ Class | _ ].
    
    
collect_relations( Result ) :- 	%X = ojciec(a,b)
    findall( predicat(Name, 2), ( op( X ), functor(X, Name, _) ), Temp ),
    delete_duplicates( Temp, Result )
	%,write('Result: '),write(Result),nl
	.

delete_duplicates( [], [] ).
delete_duplicates( [ E | R ], Out ) :-
    member( E, R ), !,
    delete_duplicates( R, Out ).
delete_duplicates( [ E | R ], [ E | Out ] ) :-
    delete_duplicates( R, Out ).    

writelist( [] ) :- nl.
writelist( [ Rule | Rest ] ) :-
    write_rule( Rule ),
    nl,
    writelist( Rest ).

write_rule( rule( P, [] ) ) :-        
    write_fact( P ),
    write( '.' ), 
    nl.
write_rule( rule( P, Q ) ) :-
    write_fact( P ),
    write( ' :- ' ),
    write_ants( Q ).
    
write_ants( [ A ] ) :-
    nl, write( '    ' ),
    write_fact( A ),
    write( '.' ).
write_ants( [ A, B | Rest ] ) :-
    nl, write( '    ' ),
    write_fact( A ),
    write( ',' ), 
    write_ants( [ B | Rest ] ).
    
write_fact( F ) :-
    F =.. [ Name | Vars ],
    write( Name ),
    write( '( ' ),
    write_vars( Vars ),
    write( ' )' ).

write_vars( [ E ] ) :-
    write_var( E ).
write_vars( [ A, B | Rest ] ) :-
    write_var( A ),
    write( ', ' ),
    write_vars( [ B | Rest ] ).
    
write_var( rule_var( I ) ) :-
    write( 'A' ),
	write(I).

max( A, B, A ) :-
    A >= B, !.
max( _, B, B ).

