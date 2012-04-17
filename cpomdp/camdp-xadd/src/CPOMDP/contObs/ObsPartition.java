package CPOMDP.contObs;

import java.util.HashMap;
import java.util.HashSet;

import xadd.XADD.Decision;
import xadd.XADD.ExprDec;

public class ObsPartition {
		double probability;
		HashMap<Decision, Boolean> decisions;
		
		
		public ObsPartition() 
		{
			decisions = new HashMap<Decision, Boolean>();
		}
		
		public ObsPartition(double probability,	HashMap<Decision, Boolean> decisions) {
			this.probability = probability;
			this.decisions = (HashMap<Decision, Boolean>) decisions.clone();
		}

		public double getProbability() {
			return probability;
		}
		public void setProbability(double probability) {
			this.probability = probability;
		}
		public HashMap<Decision, Boolean> get_decisions() {
			return decisions;
		}
		public void set_decisions(
				HashMap<Decision, Boolean> decisions) {
			this.decisions = decisions;
		}
		
		
}
