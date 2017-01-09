package ss.week6.voteMachine;

import java.util.HashMap;
import java.util.Map;
import java.util.Observable;

public class VoteList extends Observable {
	private Map<String, Integer> allVotes;
	
	public VoteList() {
		allVotes = new HashMap<String, Integer>();
	}
	
	public void addVote(String party) {
		int value = 1;
		if (allVotes.containsKey(party)) {
			value = allVotes.get(party);
		}
		allVotes.put(party, value);
		setChanged();
		notifyObservers("vote");
	}
	
	public Map<String, Integer> getVotes() {
		Map<String, Integer> toReturn = new HashMap<String, Integer>(allVotes.size());
		toReturn.putAll(allVotes);
		return toReturn;
	}

}
