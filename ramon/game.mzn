include "global_cardinality.mzn";

% ----------------------------- %
% ----  INPUT DATA ------------ %
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
% --  CONFIGURATION DATA ----- %
% ----------------------------- %

int: n_tipus; 

int: total_orientacions;
int: maxim_caselles; 

array[1..n_tipus] of int: inici_orientacions; 
array[1..n_tipus] of int: orientacions_finques; 
array[1..n_tipus] of int: caselles_finques; 

array[1..total_orientacions, 1..maxim_caselles, 1..2] of int: finques_amb_orientacions; 

% ----------------------------- %
% ---  DECISION VARIABLES ---- %
% ----------------------------- %

array[1..alcada_taulell, 1..amplada_taulell] of var 0..n_finques: taulell; % taulell means the board matrix of placed estate indexes

array[1..n_finques] of var 1..alcada_taulell: fila; % fila means starting row of each estate
array[1..n_finques] of var 1..amplada_taulell: columna; % columna means starting column of each estate
array[1..n_finques] of var 1..total_orientacions: id_orientacio; % id_orientacio means selected orientation index for each estate

% ----------------------------- %
% -------  CONSTRAINTS -------- %
% ----------------------------- %

% How it works?
% - The estates to place are iterated, and each one is placed as a whole, 
%     that is, each board cell C must match the corresponding cell F of the estate 
%     and all other cells are checked so no constraint is violated.

% Place the estates
constraint forall(f in 1..n_finques) (
    let {
        int: finca = finques[f], % finca means selected estate type 
        var int: orientacio = id_orientacio[f] % orientacio means selected orientation for this estate
    } in (
        orientacio >= inici_orientacions[finca] /\  % The orientation index in the global array is within the valid range for this estate (>= first)
        orientacio < inici_orientacions[finca] + orientacions_finques[finca] /\ % ..up to the number of orientations available for this estate
        
        forall(casella in 1..caselles_finques[finca]) ( % Check that estate cells can be placed on the board
            let {
                var int: fila_casella = fila[f] + finques_amb_orientacions[orientacio, casella, 1] - 1, % fila_casella means board row from current row plus orientation offset 
                var int: columna_casella = columna[f] + finques_amb_orientacions[orientacio, casella, 2] - 1 % columna_casella means board column from current column plus orientation offset
            } in (
                fila_casella in 1..alcada_taulell /\ columna_casella in 1..amplada_taulell /\ % The target cell is inside the board
                taulell[fila_casella, columna_casella] = f % The estate is placed there
            )
        )
    )
);

int: camins_o_parcs = (alcada_taulell * amplada_taulell) - sum(f in 1..n_finques)(caselles_finques[finques[f]]); % camins_o_parcs means cells reserved for paths or parks

% No overlapping cells (Global Cardinality)
constraint global_cardinality(
    [taulell[_fila, _columna] | _fila in 1..alcada_taulell, _columna in 1..amplada_taulell], % Each cell on the board
    [_finca | _finca in 0..n_finques], % 0 (paths or parks) plus estate IDs (1, 2, 3, 4, ...) as counted values
    [camins_o_parcs] ++ [caselles_finques[finques[_finca]] | _finca in 1..n_finques] % camins_o_parcs plus required cell count for each estate 
);

% Small optimization (minor): avoid symmetry between identical estates
constraint forall(finca1, finca2 in 1..n_finques where finca1 < finca2) ( % For each pair of estates 
    if finques[finca1] == finques[finca2] then % Same estate type appears twice
         % Eliminate symmetric solutions where equal estates are swapped
        (fila[finca1] * amplada_taulell + columna[finca1]) < (fila[finca2] * amplada_taulell + columna[finca2])
    endif
);

% Parks (cannot contain estates)
constraint forall(parc in 1..n_parcs) ( 
    taulell[parcs[parc, 1], parcs[parc, 2]] = 0  % taulell[row, column] = 0
);

% Paths (cannot contain estates)
constraint forall(cami in 1..n_camins) ( 
    taulell[camins[cami, 1], camins[cami, 2]] = 0 % taulell[row, column] = 0
);

% Estates that cannot touch
constraint forall(i in 1..n_incompatibles) ( % For each incompatible pair (one pair per row)
    let {
        int: finca1 = incompatibles[i, 1],
        int: finca2 = incompatibles[i, 2]
    } in 
    forall(_fila in 1..alcada_taulell, _columna in 1..amplada_taulell where taulell[_fila,_columna] == finca1) ( % For each cell (row, column) of the estate on the board
        forall(_offset_fila, _offset_columna in -1..1 where (_offset_fila != 0 \/ _offset_columna != 0) /\ not (_offset_fila != 0 /\ _offset_columna != 0)) ( % For each neighboring cell at Manhattan distance 1, excluding itself
        
            let {
                int: _nova_fila = _fila + _offset_fila,
                int: _nova_columna = _columna + _offset_columna
            } in (
                if _nova_fila in 1..alcada_taulell /\ _nova_columna in 1..amplada_taulell then % must belong to the board
                    taulell[_nova_fila, _nova_columna] != finca2 % Here we enforce inequality
                endif
            )
        )
    )
);

% Internal boolean matrix for parks
array[1..alcada_taulell, 1..amplada_taulell] of bool: matriu_de_parcs = array2d(1..alcada_taulell, 1..amplada_taulell, [
    exists(_parc in 1..n_parcs)(parcs[_parc,1] == _fila /\ parcs[_parc,2] == c_columna) % A park exists at this position
    | _fila in 1..alcada_taulell, c_columna in 1..amplada_taulell
]);

% Estates with park adjacency
constraint forall(_finca in finques_amb_parc) (
    exists(_fila in 1..alcada_taulell, _columna in 1..amplada_taulell where taulell[_fila, _columna] == _finca) ( % Any cell of the estate
        exists(_offset_fila, _offset_columna in -1..1 where (_offset_fila != 0 \/ _offset_columna != 0) /\ not (_offset_fila != 0 /\ _offset_columna != 0)) ( % Any neighboring cell at Manhattan distance 1, excluding itself
         
            let {
                int: _nova_fila = _fila + _offset_fila,
                int: _nova_columna = _columna + _offset_columna
            } in (
                _nova_fila in 1..alcada_taulell /\ _nova_columna in 1..amplada_taulell /\ matriu_de_parcs[_nova_fila, _nova_columna] % It must be inside the board and be a park
            )
        )
    )
);

% ----------------------------- %
% ---------  SOLVE ------------ %
% ----------------------------- %
solve :: int_search(fila ++ columna ++ id_orientacio, input_order, indomain_min) satisfy; % Search strategy over estates (fila ++ columna ++ id_orientacio), taking the smallest domain value first

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
