//Tupla
tuple Aresta {
	int ori;   //Origem
	int che;   //Chegada
};

//Conjuntos de entrada
{int} H =...; //Casas das criancas
{int} HH=...; //Uniao da casa da crianca a escola
{int} I =...; //Idade das criancas

{Aresta} A = {
    <ori, che> | ori in HH, che in HH
};

//Parametros
float dij [HH][HH]=...; //qualidade do caminho
float qki [I][H]=...; //quantidade de criancas
float pk [I] =...; //nivel de atencao
float p =...; //numero maximo de crianca por monitor
float Si[H]=...; //distancia entre a escola e a Origem
float Siii [H]=...; //porcentagem dicional
float cij [HH][HH]=...; //distancia da Origem ate a Chegada
float alpha = ...; //seguranca do trajeto
float M = ...; //numero suficientemente grande

//Variaveis de decisao
dvar int+ zi [H]; //quantidade de monitores que comecam na Origem
dvar boolean yij [HH][HH]; //1 se o caminho da Origem ate a Chegada for utilizado e 0 caso contrario
dvar int+ theta; //caminho mais longo
dvar int+ wkij [I][HH][HH]; //criancas de idade k que vao da Origem ate a Chegada
dvar int+ xij [HH][HH]; //quantidade de monitores que vao da Origem ate a Chegada 
dvar int+ Pi [H]; //distancia da Origem ate a escola

//Funcao objetivo 2
minimize
 theta + (alpha * sum(a in A) (dij[a.ori][a.che]*yij[a.ori][a.che])); //minimizar o trajeto de caminhada da crianca que mais caminha
  
//Restricoes
subject to
{
  forall (i in H) 
    forall (k in I)
    - sum (a in A : i == a.che) (wkij[k][a.ori][a.che]) + sum (a in A : i == a.ori) (wkij[k][a.ori][a.che]) == qki[k][i]; //continuidade dos caminhos para as criancas (3)
    
  forall (i in H)
    - sum (a in A : i == a.che) (xij [a.ori][a.che]) + sum (a in A : i == a.ori) xij[a.ori][a.che] == zi [i]; //continuidade dos caminhos para os monitores (4)
   
  forall (a in A)
      sum (k in I)(pk[k] * wkij[k][a.ori][a.che]) - (p * xij[a.ori][a.che]) <= 0; //numero de monitores suficiente para supervisionar as criancas (5)
      
  forall (a in A)
    yij [a.ori][a.che] - sum (k in I) (wkij[k][a.ori][a.che]) <= 0; //distancia percorrida por uma crianca ou monitor contabilizada (6)
         
  forall (a in A)
    yij [a.ori][a.che] - xij[a.ori][a.che] <= 0; //distancia percorrida por uma crianca ou monitor contabilizada (7)
    
  forall (a in A)
    xij [a.ori][a.che] - (M * yij[a.ori][a.che]) <= 0; //distancia percorrida por uma crianca ou monitor contabilizada (8)
    
  forall (i in H)
    sum (a in A : i == a.ori)(yij[a.ori][a.che]) == 1; //todos nos visitados (9)
    
  forall (i in H)
    Pi [i] <= Si[i] * Siii [i]; //distancia limite (10)
    
  forall (i in H)
    Pi [i] <= theta; //Contabiliza distancia percorrida (11)
    
  forall (a in A : a.ori != 0 && a.che != 0)
    Pi [a.che] - Pi [a.ori] + 
    ((Si[a.ori] * Siii[a.ori]) - Si[a.ori] + cij[a.ori][a.che]) * yij[a.ori][a.che] + 
    ((Si[a.che] * Siii[a.che]) - Si[a.ori] - cij[a.che][a.ori]) * yij[a.che][a.ori] <= (Si[a.che] * Siii[a.che]) - Si[a.ori]; //distancia percorrida de cada no ate a escola (12)                     
      
  forall (i in H)
    sum (a in A: i == a.che) (yij[a.ori][a.che] + zi[a.che]) >= 1; //monitores so podem comecar seu percurso em nos folhas (13)
    
  forall (a in A : a.che != 0)
    zi[a.che] - ((1 - yij[a.ori][a.che]) * M) <= 0; //monitores so podem comecar seu percurso em nos folhas (14)
    
  forall (a in A)
    forall (k in I)
      wkij [k][a.ori][a.che] >= 0; //nao negatividade (15)
      
  forall (a in A)
    forall (k in I)
      xij [a.ori][a.che] >= 0; //nao negatividade (15)
      
  forall (i in H)
    zi[i] >= 0; //nao negatividade (16)
    
  forall (i in H)
    zi[i] != 0; //nao negatividade (16)
    
  forall (i in H)
    Pi [i] >= 0; //nao negatividade (16)
    
  forall (i in H)
   Pi[i] != 0; //nao negatividade (16)
   
  theta >= 0; //nao negatividade (16)
  
  theta != 0; //nao negatividade (16)
    
};