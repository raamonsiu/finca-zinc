include "globals.mzn";

function var int: linearToRow(var int: p) = (p - 1) div width + 1;
function var int: linearToCol(var int: p) = (p - 1) mod width + 1;

% Especificació tipus de finques
int: n_tipus_finques;
set of int: Tipus_Finca = 1..n_tipus_finques;

%type Pos = tuple(int,int);
type Pos = tuple(int,int);
Pos: PAD = (0,0);

int: maxPts;

array[Tipus_Finca, 1..maxPts] of Pos: definicio_finques;

% Dimensions de la parcel·la a edificar
int: height;
int: width;

% Caselles destinades a parcs
set of int: parcs;

% Caselles destinades a camins
set of int: camins;

% Finques que s’han de posar, indicat el tipus que és
int: n_finques;
array[1..n_finques] of Tipus_Finca: finques;

% Parelles de finques que no es poden tocar
set of int: Index_Finca = 1..n_finques;

int: n_incompatibles;
type Incompatibles = tuple(Index_Finca, Index_Finca);

array[1..n_incompatibles] of Incompatibles: incompatibles;

% Finques que han de tenir com a veí una casella de parc com a mínim
set of Index_Finca: finques_amb_parc;

% Constraints sobre les entrades


% RESTRICCIONS


array[Index_Finca] of int: npts =
  [ sum(i in 1..maxPts)( bool2int(definicio_finques[finques[k], i] != PAD) )
  | k in Index_Finca ];

int: N = sum(npts);

% Podria fer certes verificacions inicials per si es pot o no, en plan mirar si hi ha suficient espai per posar les finques.
constraint N <= height*width; %Aixo no esta tenint en compte parcs i camins







array[1..N] of var 1..height*width: solucio;

% Que totes les finques estiguin posades
constraint alldifferent(solucio);

% Que cada peça estigui ben posada segons la seva definicio_finques
array[Index_Finca] of int: start = [ 1 + sum(t in 1..k-1)(npts[t]) | k in Index_Finca ]; 
function set of int: idxs(int: k) = start[k] .. start[k] + npts[k] - 1;

type D = tuple(int,int);

function var D: distancia(var int: a, var int: b) =
  ( abs(linearToRow(a) - linearToRow(b)),
    abs(linearToCol(a) - linearToCol(b)) );


function array[1..2] of D: possibles_distancies(int: k, int: i, int: j) =
  let {
    Tipus_Finca: t = finques[k],
    Pos: a = definicio_finques[t, i],
    Pos: b = definicio_finques[t, j],
    int: dr = abs(a.1 - b.1),
    int: dc = abs(a.2 - b.2)
  } in
    [ (dr, dc), (dc, dr) ];



function int: local_idx(int: k, int: g) = g - start[k] + 1;

constraint forall(k in Index_Finca)(
  forall(i, j in idxs(k) where i < j)(
    let {
      int: li = local_idx(k,i),
      int: lj = local_idx(k,j),
      var D: d = distancia(solucio[i], solucio[j]),
      array[1..2] of D: P = possibles_distancies(k, li, lj)
    } in
      (d == P[1]) \/ (d == P[2])
  )
);
% Crec que necesito 2 indexos per la distancia pero potser podria treballar tot el rato amb numeros absoluts, crec que si que es podria amb absoluts. tot i aixi no sé si es millor que no sigui absolut...


% Que no siguin ni parcs ni camins
set of int: forb = parcs union camins;
constraint forall(p in 1..N)(not (solucio[p] in forb) );


% Incompatibilitats
function var bool: adjacent4(var int: a, var int: b) =
  abs(linearToRow(a) - linearToRow(b)) + abs(linearToCol(a) - linearToCol(b)) == 1;

constraint forall(m in 1..n_incompatibles)(
  let {
    int: k1 = incompatibles[m].1,
    int: k2 = incompatibles[m].2
  } in
  forall(p1 in idxs(k1), p2 in idxs(k2))(
    not adjacent4(solucio[p1], solucio[p2])
  )
);

% finques amb parc

constraint forall(k in finques_amb_parc)(
  exists(p in idxs(k), q in parcs)(
    adjacent4(solucio[p], q)
  )
);



solve satisfy;






% OUTPUT

function var 0..n_finques: finca_of_point(var 1..N: p) =
  sum(k in Index_Finca)(
    bool2int(p >= start[k] /\ p <= start[k] + npts[k] - 1) * k
  );

array[1..height, 1..width] of var 0..N: grid =
  array2d(1..height, 1..width,
    [ if exists(k in 1..N)(linearToRow(solucio[k]) == r /\ linearToCol(solucio[k]) == c)
      then sum(k in 1..N)(
             bool2int(linearToRow(solucio[k]) == r /\ linearToCol(solucio[k]) == c) * k
           )
      else 0
      endif
    | r in 1..height, c in 1..width ]);

output [
  "Graella per finques (0=buit, 1..n_finques=id finca)\n",
  concat([ concat([
            let { int: p = fix(grid[r,c]) } in
              (if p == 0 then " 0 "
               else
                 let { int: v = fix(finques[finca_of_point(p)]) } in
                   (if v < 10 then " " else "" endif) ++ show(v) ++ " "
               endif)
          | c in 1..width ]) ++ "\n"
        | r in 1..height ])
];






