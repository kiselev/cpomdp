package CPOMDP;

import xadd.XADD.ArithExpr;
import xadd.XADD.CompExpr;

public class StateObsVector {
		Double probability;
		CompExpr state;
		CompExpr obs; 
		
		public StateObsVector(CompExpr s,CompExpr o,Double p)
		{
			state = s;
			obs = o;
			probability = p;
		}
		public CompExpr getState() {
			return state;
		}

		public void setState(CompExpr state) {
			this.state = state;
		}

		public CompExpr getObs() {
			return obs;
		}

		public void setObs(CompExpr obs) {
			this.obs = obs;
		}
		public Double getProbability() {
			return probability;
		}

		public void setProbability(Double probability) {
			this.probability = probability;
		}
}
