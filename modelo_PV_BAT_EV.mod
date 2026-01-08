# MODELO

# Definição de conjuntos
set NODOS; # Conjunto de nós 
set C within NODOS; # Conjunto de clientes
set D within NODOS; # Conjunto de depósitos
set Q within NODOS; # Conjunto de estações de recarga
set CQ := C union Q;
set H:= 1..24;  # Conjunto de horas no dia
set S; # Conjunto de cenários total
set SN; # Conjunto de cenários normais
set SE; # Conjunto de cenários extremos

# Definição dos parâmetros
param d{NODOS, NODOS}; # Distância entre os nós
param n:= card(NODOS); # Número total de nós
param v_max; # Velocidade constante do VE  
param eta_c_BAT; # Eficiência de carregamento das baterias
param eta_d_BAT; # Eficiência de descarregamento das baterias
param eta_c_VE; # Eficiência de carregamento do VE
param eta_d_VE; # Eficiência de descarregamento do VE
param tau_CHmax; # Tempo máximo de carregamento do VE
param tau_CHmin; # Tempo mínimo de carregamento VE
param Pcargamax; # Potência máxima de carregamento do VE
param SOC_inicial; # SOC inicial do VE
param SOC_max; # SOC máximo do VE 
param SOC_min; # SOC mínimo do VE 
param consumo; # Taxa de consumo de energia por distância
param TMAX; # Tempo máximo de operação do VE
param Noct; # Temperatura nominal do painel fotovoltaico
param Voc;  # Tensão de circuito aberto
param Isc;  # Corrente de curto circuito
param Kv; # Coeficiente de temperatura para a tensão
param Ki; # Coeficiente de temperatura para a corrente
param Vmppt; # Tensão  em ponto de máxima potência
param Imppt;  # Corrente em ponto de máxima potência
param Ta; # Temperatura ambiente
param c_p; # Custo de cada painel fotovoltaico
param c_b; # Custo de cada bateria
param c_d; # Custo associado ao uso do VE - despesas com motorista, percurso da rota (R$/km)
param P_BAT_nom; # Potência nominal de cada bateria
param G{H,S}; # Perfil de irradiação solar
param Tc{H,S} >= 0; # Temperatura na célula fotovoltaica
param Ic{H,S} >= 0; # Corrente na célula fotovoltaica
param Vc{H,S} >= 0; # Tensão na célula fotovoltaica
param P_pv_m{H,S} >= 0; # Potência fotovoltaica máxima disponível
param FF >= 0; # Fator de forma
param E_BAT_nom >= 0; # Energia da bateria nominal
param pi{S} >= 0; # Fator de peso para os cenários
param vida_util >= 0; # Vida útil da bateria do VE
param taxa_juros >=0; # Taxa de juros ao ano
param dias_ano >= 0; # Dias úteis por ano
param alpha >= 0; # Parâmetro que cálcula a taxa para trazer ao valor presente
param lambda;
param lambda2;
param omega;

# Definição das variáveis
var x{NODOS, NODOS} binary; # Variável binaria para indicar os arcos ativos
var U{NODOS} >= 0; # Variável fictícia para eliminar subtour
var t{NODOS, NODOS} >=0; # Variável que representa o tempo de percurso do arco xijk
var SOC{NODOS} >= 0; # Variável que representa o estado de carga de saída do VE do nó
var SOC_a{NODOS} >= 0; # Variável que representa o estado de carga do VE de chegada ao nó
var tau_CH {S} >= 0; # Variável que representa o tempo de carga do VE;
var delta {NODOS, NODOS} >= 0; # Variável auxiliar para linearizar o produto entre x e SOC
var z integer >= 0 <= 1000; # Variável binária de instalação de painéis fotovoltaicos
var y integer >= 0 <= 100; # Variavel binaria de instalação de baterias
var P_BAT_c {H,S} >= 0; # Potência de carga de cada bateria
var P_BAT_d {H,S} >= 0; # Potência de descarga de cada bateria
var E_BAT {H,S} >= 0; # Energia de cada bateria
var P_pv{H,S} >= 0; # Potência fotovoltaica total 
var Pcarga{H,S} >= 0; # Variável pra armazenar a potência necessária para carregar  VE
var t_aux{NODOS,NODOS} >= 0; 
var tn{NODOS} >= 0;
var beta{H} binary;
var gama{H,S} binary;
var P_virtual{H,SE} >= 0;

# FUNÇÃO OBJETIVO
#(1º termo: minimiza o custo da instalação de paineis fotovoltaicos, 2º termo: minimiza o custo da instalação de baterias, 3º termo: minimiza o custo de operação do VE)
minimize fo:
    z * c_p + y * c_b  +
    dias_ano * c_d * alpha * sum{i in NODOS, j in NODOS} d[i,j]*x[i,j] +
    lambda*sum{s in S} pi[s]*(tau_CH[s] + sum{i in NODOS, j in NODOS} d[i,j]/v_max*x[i,j]) +
    lambda2*sum{s in SE, h in H} pi[s]*P_virtual[h,s] ;

##########################################################################
# RESTRIÇÕES

 # Percorre todos os nós apenas uma vez
subject to restricao1 {j in CQ}:
	sum {i in NODOS} x[i,j] = 1;
	
# Sai do depósito apenas uma vez
subject to restricao2 {i in D}:
	sum{j in CQ} x[i,j] = 1;

# Volta ao depósito apenas uma vez
subject to restricao3 {i in D}:
	sum{j in CQ} x[j,i] = 1;

# Conectividade entre os arcos
subject to restricao4 {i in NODOS}:
	sum{j in NODOS} x[i,j] - sum {j in NODOS} x[j,i] = 0;

# Não permite duplicação dos arcos
subject to restricao5 {i in NODOS, j in NODOS}:
	x[i,j] + x[j,i] <= 1; 

# Elimina subtour	
subject to restricao6 {i in CQ, j in CQ}:
	U[i] - U[j] + (n-1)*x[i,j] <= n - 2;
	
	
##### restrições do tempo
	
# iniciando a variavel de tempo no nós em 8 da manhã
subject to restricao7 {i in D}:
	tn[i] = 8;			

## Linearização do cálculo do tempo de chegada em cada nó

# o tempo de chegada no nó j vai ser igual a soma dos tempo de percurso entre os nós anteriores
subject to restricao8 {j in CQ}:
  tn[j] = sum{i in NODOS} t_aux[i,j];
	
# o tempo de chegada do no anterior (i) mais o tempo de percurso entre os nois i e j tem que ser maior q 0 
subject to restricao9 {i in NODOS, j in CQ}:
  0 <= tn[i] + d[i,j]/v_max*x[i,j]  - t_aux[i,j];

# o tempo de chegada do no anterior (i) mais o tempo de percurso entre os nois i e j tem que ser menor que um tempo máximo de operação
subject to restricao10 {i in NODOS, j in CQ}:
  tn[i] + d[i,j]/v_max*x[i,j]  - t_aux[i,j] <= TMAX*(1-x[i,j]);

# limite superior da variavel t_aux
subject to restricao11 {i in NODOS, j in CQ}:
  t_aux[i,j] <= TMAX*x[i,j];	
				
# Limita que o tempo de percurso mais o tempo de recarga seja menor ou igual a um tempo máximo de operação
subject to restricao12 {i in NODOS, s in S}:
	tn[i] + tau_CH[s] <= TMAX;

 # Limita o tempo de carga do VE a um valor máximo e mínimo
# subject to restricao13 {s in S}:
	# tau_CH[s] <= tau_CHmax;
# subject to restricao14 {s in S}:
	# tau_CH[s] >= tau_CHmin;
	
## restrições para definir o tempo que fica na estação carregando
# variavel binária para armazenar a que horas em que chega a estação
subject to restricao15:
	sum{h in H} beta[h] = 1;

# aproxima os valores de beta para o intervalo horário em que chega na estação
subject to restricao16 {j in Q}:
	sum{h in H} h * beta[h] <= tn[j]+ 1;	
subject to restricao17 {j in Q}:
	tn[j] + 1 <= sum{h in H} h * beta[h] + 1; 	
	
# variavel binária que vai receber valor de 1 a partir do momento em que chega na estação de recarga 
subject to restricao18 {h in H, s in S}:
	gama[h,s] <= sum {k in H: k <= h} beta[k];	
	
# gama vai continuar recebendo valor de 1 enquanto o veículo estiver na estação e a partir do momento que chegou
subject to restricao19 {h in H, s in S, j in Q}:
	h * gama[h,s] <= tn[j] + tau_CH[s];	

# gama vai continuar recebendo valor de 1 durante o tempo de carregamento (tau)
subject to restricao20 {s in S}:
	sum{h in H} gama[h,s] <= tau_CH[s] + 1;
subject to restricao21 {s in S}:
	tau_CH[s] + 1 <= sum{h in H} gama[h,s] + 1;	
	
# a quantidade de horas que fica na estação nao pode ser maior que o tempo de carregamento máximo
# subject to restricao22 {s in S}:
	# sum{h in H} gama[h,s] <= tau_CHmax; 

############
## restrições do estado de carga do VE

# Define um estado de carga inicial para o VE
subject to restricao23{i in D}:
	SOC[i] = SOC_inicial;

# Limita o estado de carga de saída do VE a um valor máximo e minimo
subject to restricao24 {j in CQ}:
	SOC[j] >= SOC_min;
subject to restricao25 {j in CQ}:
	SOC[j] <= SOC_max;
	
# Limita o estado de carga de chegada ao nó a um valor máximo e minimo
subject to restricao26 {j in NODOS}:
	SOC_a[j] >= SOC_min;
subject to restricao27 {j in NODOS}:
	SOC_a[j] <= SOC_max;
	
# Calcula o estado de carga de saida da estação de recarga: o que chegou + o que carregou
subject to restricao28 {j in Q, s in S, se in SE}:
	SOC[j] = SOC_a[j] + sum {h in H} (Pcarga[h,s] + P_virtual[h,se])* eta_c_VE; 

# Nos nós de clientes, o estado de carga de chegada é igual ao de saída
subject to restricao29 {j in C}:
	SOC[j] = SOC_a[j]; 


# Calcula o estado de carga de chegada em cada nó
subject to restricao30 {j in NODOS}:
	SOC_a[j] = sum {i in NODOS} delta[i,j] - sum {i in NODOS} x[i,j] / eta_d_VE * consumo * d[i,j];

# Linearização do calculo do soc de chegada em cada nó
subject to linearizacao1 {i in NODOS, j in NODOS}:
	0 <=  delta[i,j];
subject to linearizacao2 {i in NODOS, j in NODOS}:
	delta[i,j] <= SOC_max * x[i,j];
subject to linearizacao3 {i in NODOS, j in NODOS}:
	0 <= SOC[i] - delta[i,j];
subject to linearizacao4 {i in NODOS, j in NODOS}:
	SOC[i] - delta[i,j] <= SOC_max * (1 - x[i,j]);  
 
###################
# restrições de potência e energia

# a potência de carregamento do VE, Pcarga é limitada ao quanto o 
# VE pode carregar por hora e quantas horas ficou na estação de recarga
subject to restricao31 {h in H, s in S}:
	Pcarga[h,s] <= Pcargamax * gama[h,s];

# define o número de baterias
subject to restricao32 {h in H, s in S}:
	P_BAT_d[h,s] + P_BAT_c[h,s] <= P_BAT_nom * y;
	
# Limita a potência de carga e de descarga das baterias a um máximo - de acordo com a variável de instalação de baterias (y)
subject to restricao33 {h in H, s in S}:
	P_BAT_c[h,s] <= P_BAT_nom * y;
subject to restricao34 {h in H, s in S}:
	P_BAT_d[h,s] <= P_BAT_nom * y;

# Limita a energia das baterias a um valor nominal
subject to restricao35 {h in H, s in S}:
	E_BAT[h,s] <= E_BAT_nom * y;

# Calcula a energia de cada bateria no inicio
subject to restricao36 {s in S, h in H : h==1}:
	E_BAT[h,s] - E_BAT_nom*omega*y = eta_c_BAT*P_BAT_c[h,s] - 1/eta_d_BAT*P_BAT_d[h,s];

# Calcula a energia de cada bateria - quando não é estado inicial
subject to restricao37 {s in S, h in H : h>1}:
	E_BAT[h,s] - E_BAT[h-1, s] = eta_c_BAT*P_BAT_c[h,s] - 1/eta_d_BAT*P_BAT_d[h,s];

# Define que a energia da bateria ao final do dia deve ser igual ao valor nominal
subject to restricao38 {s in SN, h in H: h == 24}:
	E_BAT[h,s] >= E_BAT_nom*omega * y;

# Balanco de potência total: (Geração: a potência gerada pelos paineis + a potência de descarga das baterias) = (Demanda: potência consumida pelos VEs)
subject to restricao39 {h in H,s in S, se in SE}:
	z * P_pv_m[h,s] + P_BAT_d[h,s] + P_virtual[h,se] >=  P_BAT_c[h,s] + Pcarga[h,s];
	
######%%%%%%%%%%%%%%%%%%$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
######%%%%%%%%%%%%%%%%%%$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
######%%%%%%%%%%%%%%%%%%$$$$$$$$$$$$$$$$$$$$$$$$$$$$$

# esta restrição obriga que a energia disponível no veículo +
# a energia disponível na microrrede seja maior ou igual para suprir
# o que o veículo precisa para completar toda a rota
# subject to restricao_energia_minima {s in S}:
  # SOC_inicial-SOC_min +
    # eta_c_VE*sum{h in H} (z * P_pv_m[h,s] + P_virtual[h,s] + P_BAT_d[h,s]-P_BAT_c[h,s])
     # >= sum {i in NODOS, j in NODOS} consumo/eta_d_VE*d[i,j]*x[i,j];

######%%%%%%%%%%%%%%%%%%$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
######%%%%%%%%%%%%%%%%%%$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
######%%%%%%%%%%%%%%%%%%$$$$$$$$$$$$$$$$$$$$$$$$$$$$$



subject to restricaopotenciavirtual {h in H, s in SE}:
	P_virtual[h,s] >= 0;
subject to restricaopotenciavirtual2 {h in H, s in SE}:
	P_virtual[h,s] <= Pcargamax;