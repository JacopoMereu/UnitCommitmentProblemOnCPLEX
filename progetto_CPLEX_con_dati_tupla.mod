/*********************************************
 * OPL 12.10.0.0 Model
 * Author: Jacopo
 * Creation Date: 23 lug 2022 at 18:09:28
 *********************************************/
 
// Input dati del problema
int nUnita = ...;
int nPeriodi = ...;

range I = 1..nUnita;
range T = 1..nPeriodi;

int D[T] = ...;


tuple dati_unita
{
	float k1;
	float k2;
	float k3;
	
	int Pmin;
	int Pmax;

	int initial_status;
	
	int min_switch_up;
	int min_switch_down;
	
	int startup_cost;
}
dati_unita unita[I] = ...;

// Variabili
dvar boolean u[I][T];
dvar int p[I][T];

// F.O.
minimize
(
	  sum (i in I, t in T) (u[i][t]*unita[i].k1 + unita[i].k2*p[i][t]+unita[i].k3*p[i][t]^2)
	  +
	  sum (i in I) (
	      u[i][1]*(unita[i].initial_status<=-1)*unita[i].startup_cost 
		  +
		  sum(t in T: t>1) (
				(u[i][t]==1 && u[i][t-1]==0) * unita[i].startup_cost 
			)
	  )
); 
	  
// VINCOLI
subject to
{
  	// V.1
    forall (t in T) 		vincolo_domanda_soddisfatta: 			sum(i in I) p[i][t] == D[t];
    
    // V.5  
	forall (i in I, t in T) vincolo_inf_potenza_prodotta_vincolata: (u[i][t]*unita[i].Pmin) <= p[i][t];
	// V.6
	forall (i in I, t in T) vincolo_sup_potenza_prodotta_vincolata:	p[i][t] <= (u[i][t]*unita[i].Pmax);			
	
	// V.9 (considerando V.11)
	vincolo_switch_up_minimo:
	forall (i in I, t in T)
		forall (r in t-unita[i].min_switch_up+1..t-1) {
				if (r<1)(u[i][t]>=
					// (x <=|S|)*[(S>0)-(S<0)]+(S<0) with X=(-r+1) ... mi permette di ottenere la variabile decisionale u[i][r] con r non positivo
					(((-r+1)<=abs(unita[i].initial_status))*((unita[i].initial_status>= 1)-(unita[i].initial_status<=-1))+(unita[i].initial_status<=-1))
				);
				if(r==1) (u[i][t] >= u[i][r]-(unita[i].initial_status>=1));		
				if(r>1) (u[i][t] >= (u[i][r]-u[i][r-1]));
	}
			
	// V.10 (considerando V.11)
	vincolo_switch_down_minimo:
	forall (i in I, t in T)
			forall (r in t-unita[i].min_switch_down+1..t-1) {
				if(r<1) u[i][t] <= (1
				 - 	(((-r+2)<=abs(unita[i].initial_status))*((unita[i].initial_status>= 1)-(unita[i].initial_status<=-1))+(unita[i].initial_status<=-1))
				 +  (((-r+1)<=abs(unita[i].initial_status))*((unita[i].initial_status>= 1)-(unita[i].initial_status<=-1))+(unita[i].initial_status<=-1))
				);
				if(r==1)u[i][t] <= (1 - (unita[i].initial_status>=1) + u[i][r]);
				if(r>1) u[i][t] <= (1 - u[i][r-1] + u[i][r]);
	}
}

