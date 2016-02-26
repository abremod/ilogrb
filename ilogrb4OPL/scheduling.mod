int RequiredLotSize = ...;  // Use 0 for no lot sizes, positive # otherwise

int Nperiods = 4;
range Periods   = 1..Nperiods;
range ZPeriods  = 0..Nperiods;
range Products  = 1..2;
range Factories = 1..2;
range Stages    = 2..3;

float Demand[Stages, Products, Periods] = ...;
float ProdCost[Factories, Products] = ...;
float ProdTime[Factories, Products] = ...;  // Unit is hours
float HoldCost = ...;
float MovCost_FDC[Factories] = ...;
float MovCost_FC[Factories] = ...;
float MovCost_DCC = ...;
int MovTime = 1;   // Unit is weeks
float TardCost_DC[Products] = ...;
float TardCost_C[Products] = ...;
float Penalty = ...;

tuple LBorUB {
   string     type;
   int        F;
   int        S;
   int        P;
   float      v;
}

setof(LBorUB) bnds = ...;

float MaxProduction = sum (k in Stages, j in Products, t in Periods) Demand[k,j,t];



int  LotSize = maxl(RequiredLotSize, 1);

dvar float+    x[Factories, Products, Periods];
dvar int+      y[Factories, Stages, Products, Periods] in 0..maxint;
dvar float+    z[Products, Periods];
dvar float+    q2[Products, ZPeriods];
dvar float+    v2[Products, Periods];
dvar float+    v3[Products, ZPeriods];
dvar boolean   yb[bnds, Periods];
dvar boolean   q2b[Products, Periods];
dvar boolean   v2b[Products, Periods];
dvar boolean   v3b[Products, Periods];
dvar int       xlots[Factories, Products, Periods] in 0 .. ftoi(MaxProduction/LotSize);

minimize
   sum (t in Periods, j in Products, i in Factories) ProdCost[i,j]*x[i,j,t] +
   sum (t in Periods, j in Products, i in Factories) MovCost_FDC[i]*y[i,2,j,t] +
   sum (t in Periods, j in Products, i in Factories) MovCost_FC[i]*y[i,3,j,t] +
   sum (t in Periods, j in Products)                 MovCost_DCC*z[j,t] +
   sum (t in Periods, j in Products)                 HoldCost*q2[j,t] +
   sum (t in 1 .. Nperiods-1, j in Products)         7*TardCost_DC[j]*v2[j,t] +
   sum (t in 1 .. Nperiods-1, j in Products)         7*TardCost_C[j]*v3[j,t] +
   sum (j in Products)                               Penalty*(v2[j,Nperiods] + v3[j,Nperiods])
;
subject to
{
   if (RequiredLotSize > 0)
      forall (i in Factories, j in Products, t in Periods)
         x[i,j,t] == RequiredLotSize*xlots[i,j,t];
   else
      forall (i in Factories, j in Products, t in Periods)
         xlots[i,j,t] == 0;
         
   // Production Capacity
   forall (t in Periods, i in Factories)
      sum (j in Products) ProdTime[i,j]*x[i,j,t] <= 168;
   
   // Disjunctive bounds for lower bounds, or specified upper bounds.
   forall (b in bnds, t in Periods) {
      if (b.type == "L") {
         y[b.F, b.S, b.P, t] >= yb[b,t]*b.v;
         y[b.F, b.S, b.P, t] <= yb[b,t]*MaxProduction;
      }
      if (b.type == "U") {
         y[b.F, b.S, b.P, t] <= b.v;
         yb[b,t] == 0;
      }
   }
   
   // Transportation constraints
   forall (t in Periods, j in Products, i in Factories)
      sum (l in Stages) y[i,l,j,t] == x[i,j,t];
   
   forall (t in Periods, j in Products : t < 4)
      sum (i in Factories) y[i,3,j,t] + z[j,t] <= Demand[3,j,t+1] + v3[j,t];
   
   forall (j in Products)
      z[j,1] <= q2[j,0];  // RHS should be max(0,q2[j,0]), but this is the same
   
   forall (t in Periods, j in Products : t > 1)
      z[j,t] <= q2[j,t-1] + sum (i in Factories) y[i,2,j,t-1];
   
   // Rule for converting constraints
   // If you have
   //   y == max(x,0), where x and y are decision variables, or x is an expression
   //                 based on decision variables, and y >= 0
   //   create a binary xb and add constraints
   //   y >= x
   //   y <= M*xb
   //   y <= x + M - M*xb
   
   // Storage constraints
   forall (j in Products) {
      q2[j,1] >= q2[j,0] - Demand[2,j,1] - z[j,1];
      q2[j,1] <= q2b[j,1]*MaxProduction;
      q2[j,1] <= q2[j,0] - Demand[2,j,1] - z[j,1] + MaxProduction - MaxProduction*q2b[j,1];
      forall (t in Periods : t > 1) {
         q2[j,t] >= q2[j,t-1] + sum (i in Factories) y[i,2,j,t-1] - Demand[2,j,t] - z[j,t] - v2[j,t-1];
         q2[j,t] <= q2b[j,t]*MaxProduction;
         q2[j,t] <= q2[j,t-1] + sum (i in Factories) y[i,2,j,t-1] - Demand[2,j,t] - z[j,t] -v2[j,t-1] + MaxProduction*(1.0-q2b[j,t]);
      }
   }
   
   // Tardy and jobs not delivered
   forall (j in Products) {
      v2[j,1] >= Demand[2,j,1] - q2[j,0];
      v2[j,1] <= v2b[j,1]*MaxProduction;
      v2[j,1] <= Demand[2,j,1] - q2[j,0] + MaxProduction*(1.0-v2b[j,1]);
      
      v3[j,1] >= Demand[3,j,1];
      v3[j,1] <= v3b[j,1]*MaxProduction;
      v3[j,1] <= Demand[3,j,1] + MaxProduction*(1.0-v3b[j,1]);
      
      forall (t in Periods : t > 1) {
         v2[j,t] >= Demand[2,j,t] + v2[j,t-1] + z[j,t] - q2[j,t] - sum(i in Factories) y[i,2,j,t-1];
         v2[j,t] <= v2b[j,t]*MaxProduction;
         v2[j,t] <= Demand[2,j,t] + v2[j,t-1] + z[j,t] - q2[j,t] - sum(i in Factories) y[i,2,j,t-1] + MaxProduction*(1.0-v2b[j,t]);
         
         v3[j,t] >= Demand[3,j,t] + v3[j,t-1] - z[j,t-1] - sum(i in Factories) y[i,3,j,t-1];
         v3[j,t] <= MaxProduction*v3b[j,t];
         v3[j,t] <= Demand[3,j,t] + v3[j,t-1] - z[j,t-1] - sum(i in Factories) y[i,3,j,t-1] + MaxProduction*(1.0-v3b[j,t]);
      }
   }
   
   // Boundary condition
   forall (j in Products) {
      v3[j,0] == 0;
      q2[j,0] == 0;
   }
         
   
}

// Report solution values
float TotProdCost    = sum (t in Periods, j in Products, i in Factories) ProdCost[i,j]*x[i,j,t];
float TotMovCost_FDC = sum (t in Periods, j in Products, i in Factories) MovCost_FDC[i]*y[i,2,j,t];
float TotMovCost_FC  = sum (t in Periods, j in Products, i in Factories) MovCost_FC[i]*y[i,3,j,t];
float TotMovCost_DCC = sum (t in Periods, j in Products)                 MovCost_DCC*z[j,t];
float TotHoldCost    = sum (t in Periods, j in Products)                 HoldCost*q2[j,t];
float TotTardCost_DC = sum (t in 1..Nperiods-1, j in Products)       7*TardCost_DC[j]*v2[j,t];
float TotTardCost_C  = sum (t in 1..Nperiods-1, j in Products)       7*TardCost_C[j]*v3[j,t];
float TotPenalty     = sum (j in Products)                               Penalty*(v2[j,Nperiods] + v3[j,Nperiods]);

float TotY[i in Factories, k in Stages, t in Periods] = sum (j in Products) y[i,k,j,t];

execute DISPLAY {
   writeln("Total Production Cost:  ", TotProdCost);
   writeln("Total Move Cost FDC:    ", TotMovCost_FDC);
   writeln("Total Move Cost FC:     ", TotMovCost_FC);
   writeln("Total Move Cost DCC:    ", TotMovCost_DCC);
   writeln("Total Hold Cost:        ", TotHoldCost);
   writeln("Total Tardy Cost DC:    ", TotTardCost_DC);
   writeln("Total Tardy Cost C:     ", TotTardCost_C);
   writeln("Total Penalty:          ", TotPenalty);
   
   for (i in Factories)
      for (k in Stages)
         for (t in Periods)
            writeln("y[", i, ",", k, ",*,", t, "] = ", TotY[i][k][t]);
}
