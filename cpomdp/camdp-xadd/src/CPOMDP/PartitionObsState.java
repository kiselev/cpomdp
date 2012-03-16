package CPOMDP;

import java.util.HashMap;

public class PartitionObsState {
		HashMap <Integer, StateObsVector> _relObsProb ;
		
		public PartitionObsState()
		{
			_relObsProb = new HashMap<Integer, StateObsVector>(); 
		}
		
		public void setnewPartition(StateObsVector so)
		{
			_relObsProb.put(_relObsProb.size(),so);
		}
	
		public int sizePartitionObsState()
		{
			return _relObsProb.size();
		}

		public HashMap<Integer, StateObsVector> get_relObsProb() {
			return _relObsProb;
		}

		public void set_relObsProb(HashMap<Integer, StateObsVector> _relObsProb) {
			this._relObsProb = _relObsProb;
		}
		
		public StateObsVector get_relObsProb(int j) {
			return _relObsProb.get(j);
		}

		public void set_relObsProb(StateObsVector so) {
			this._relObsProb.put(_relObsProb.size(), so);
		}
}
