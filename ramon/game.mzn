include "global_cardinality.mzn";

% ----------------------------- %
% ----  DADES D'ENTRADA ------- %
% ----------------------------- %
int: alcada_taulell; 
int: amplada_taulell; 

int: n_finques; 
array[1..n_finques] of int: finques; 

int: n_parcs;
array[1..n_parcs, 1..2] of int: parcs;

int: n_camins;
array[1..n_camins, 1..2] of int: camins;

int: n_incompatibles;
array[1..n_incompatibles, 1..2] of 1..n_finques: incompatibles;

set of int: finques_amb_parc;

% ----------------------------- %
% --  DADES DE CONFIGURACIÓ --- %
% ----------------------------- %

int: n_tipus; 

int: total_orientacions;
int: maxim_caselles; 

array[1..n_tipus] of int: inici_orientacions; 
array[1..n_tipus] of int: orientacions_finques; 
array[1..n_tipus] of int: caselles_finques; 

array[1..total_orientacions, 1..maxim_caselles, 1..2] of int: finques_amb_orientacions; 

% ----------------------------- %
% ---  VARIABLES DE DESISIÓ --- %
% ----------------------------- %

array[1..alcada_taulell, 1..amplada_taulell] of var 0..n_finques: taulell; % Taulell

array[1..n_finques] of var 1..alcada_taulell: fila; % Fila de la casella inicial de cada finca
array[1..n_finques] of var 1..amplada_taulell: columna; % Columna de la casella inicial de cada finca
array[1..n_finques] of var 1..total_orientacions: id_orientacio; % Orientació de cada finca

% ----------------------------- %
% -------  CONSTRAINTS -------- %
% ----------------------------- %

% Com funciona?
% - Es recorren les finques que s'han de posar, i s'intenten posar SENCERES, 
%     és a dir, en una cassella C del taulell ha d'anar la cassella F de la finca 
%     i comprovar que totes les altres casselles no trenquen cap restricció i així les podem posar.

% Colocar les finques
constraint forall(f in 1..n_finques) (
    let {
        int: finca = finques[f], % Finca 
        var int: orientacio = id_orientacio[f] % Orientació de la finca
    } in (
        orientacio >= inici_orientacions[finca] /\  % La orientació (de l'array de totes les orientacions) pertany al rang de la finca (>= primer)
        orientacio < inici_orientacions[finca] + orientacions_finques[finca] /\ % ...fins al nombre d'orientacions que té aquesta finca
        
        forall(casella in 1..caselles_finques[finca]) ( % Mirem que les casselles es puguin posar al taulell
            let {
                var int: fila_casella = fila[f] + finques_amb_orientacions[orientacio, casella, 1] - 1, % Agafem la fila de la cassella partint de la fila actual + l'offset del model 
                var int: columna_casella = columna[f] + finques_amb_orientacions[orientacio, casella, 2] - 1 % Lo mateix amb columna
            } in (
                fila_casella in 1..alcada_taulell /\ columna_casella in 1..amplada_taulell /\ % La casella adient està dins el taulell
                taulell[fila_casella, columna_casella] = f % Hi posem la finca
            )
        )
    )
);

int: camins_o_parcs = (alcada_taulell * amplada_taulell) - sum(f in 1..n_finques)(caselles_finques[finques[f]]); % Son les que haurien de tenir parc o cami

% No solapar casselles (Global Cardinality)
constraint global_cardinality(
    [taulell[_fila, _columna] | _fila in 1..alcada_taulell, _columna in 1..amplada_taulell], % Cada cassella del taulell
    [_finca | _finca in 0..n_finques], % 0(camins o parcs) ++ Valors de finques (1, 2, 3, 4, ...) -> Lo que controlem
    [camins_o_parcs] ++ [caselles_finques[finques[_finca]] | _finca in 1..n_finques] % camins_o_parcs + caselles_finques[finques[_finca]] per a cada finca 
);

% Extra per optimitzar una mica (despreciable) Evitar dualitat entre finques iguals
constraint forall(finca1, finca2 in 1..n_finques where finca1 < finca2) ( % Per a cada parella de finques 
    if finques[finca1] == finques[finca2] then % La mateixa finca 2 cops
         % Eliminar la possibilitat de comptar 2 solucions amb les finques intercanviades (seria lo mateix)
        (fila[finca1] * amplada_taulell + columna[finca1]) < (fila[finca2] * amplada_taulell + columna[finca2])
    endif
);

% Parcs (no pot haver finca)
constraint forall(parc in 1..n_parcs) ( 
    taulell[parcs[parc, 1], parcs[parc, 2]] = 0  % Taulell[fila, columna] = 0
);

% Camins (no pot haver finca)
constraint forall(cami in 1..n_camins) ( 
    taulell[camins[cami, 1], camins[cami, 2]] = 0 % Taulell[fila, columna] = 0
);

% Finques que no es poden tocar
constraint forall(i in 1..n_incompatibles) ( % Per a cada parella de incompatibles (cada poarella es una fila)
    let {
        int: finca1 = incompatibles[i, 1],
        int: finca2 = incompatibles[i, 2]
    } in 
    forall(_fila in 1..alcada_taulell, _columna in 1..amplada_taulell where taulell[_fila,_columna] == finca1) ( % Per a cada casella (fila, columna) de la finca en el taulell
        forall(_offset_fila, _offset_columna in -1..1 where _offset_fila != 0 \/ _offset_columna != 0) ( % Per a cada casella a dinstància 1 (veina) menys la cassella en si (quan ambdós són 0)
          % NOTA IMPORTANT: Si no contem la diagonal com a veí, posar XOR = [(_offset_fila != 0 \/ _offset_columna != 0) /\ not (_offset_fila != 0 /\ _offset_columna != 0]
            let {
                int: _nova_fila = _fila + _offset_fila,
                int: _nova_columna = _columna + _offset_columna
            } in (
                if _nova_fila in 1..alcada_taulell /\ _nova_columna in 1..amplada_taulell then % ha de pertanyer al taulell
                    taulell[_nova_fila, _nova_columna] != finca2 % Aquí mirem diferent
                endif
            )
        )
    )
);

% Matriu booleana interna per als parcs
array[1..alcada_taulell, 1..amplada_taulell] of bool: matriu_de_parcs = array2d(1..alcada_taulell, 1..amplada_taulell, [
    exists(_parc in 1..n_parcs)(parcs[_parc,1] == _fila /\ parcs[_parc,2] == c_columna) % Existeix un parc que t'e aquesta posicio
    | _fila in 1..alcada_taulell, c_columna in 1..amplada_taulell
]);

% Finques amb parc
constraint forall(_finca in finques_amb_parc) (
    exists(_fila in 1..alcada_taulell, _columna in 1..amplada_taulell where taulell[_fila, _columna] == _finca) ( % Qualsevol de les casseles de la finca
        exists(_offset_fila, _offset_columna in -1..1 where _offset_fila != 0 \/ _offset_columna != 0) ( % Qualsevol casella a dinstància 1 (veina) menys la cassella en si (quan ambdós són 0)
          % NOTA IMPORTANT: Si no contem la diagonal com a veí, posar XOR = [(_offset_fila != 0 \/ _offset_columna != 0) /\ not (_offset_fila != 0 /\ _offset_columna != 0]
            let {
                int: _nova_fila = _fila + _offset_fila,
                int: _nova_columna = _columna + _offset_columna
            } in (
                _nova_fila in 1..alcada_taulell /\ _nova_columna in 1..amplada_taulell /\ matriu_de_parcs[_nova_fila, _nova_columna] % Ha d'estar dins el taulell i ser un parc
            )
        )
    )
);

% ----------------------------- %
% ---------  SOLVE ------------ %
% ----------------------------- %
solve :: int_search(fila ++ columna ++ id_orientacio, first_fail, indomain_min) satisfy; % Cerca per prioritat (first_fail) orientada a finques, no a caselles (fila ++ columna ++ id_odietacio). indomain_prova el valor m'es petit del domini primer

% ----------------------------- %
% --------  OUTPUT ------------ %
% ----------------------------- %
output [
    if interador_columna = 1 then "\n" else "" endif ++
    let {
        int: valor = fix(taulell[iterador_fila,interador_columna]),
        bool: p = exists(k in 1..n_parcs)(parcs[k,1]==iterador_fila /\ parcs[k,2]==interador_columna),
        bool: c = exists(k in 1..n_camins)(camins[k,1]==iterador_fila /\ camins[k,2]==interador_columna)
    } in (
        if p then "Parc  "
        elseif c then "Cami  "
        elseif valor == 0 then ".     "
        elseif valor < 10 then show(valor) ++ "     "
        else show(valor) ++ "    " endif
    )
    | iterador_fila in 1..alcada_taulell, interador_columna in 1..amplada_taulell
] ++ ["\n"];