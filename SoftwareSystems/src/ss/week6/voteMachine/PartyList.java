package ss.week6.voteMachine;

import java.util.ArrayList;
import java.util.List;
import java.util.Observable;

public class PartyList extends Observable {
	private List<String> parties;
	
	public PartyList() {
		parties = new ArrayList<String>();
	}
	
	public void addParty(String partyName) {
		if (partyName != null && partyName.length() > 0 && !parties.contains(partyName))  {
			parties.add(partyName);
			setChanged();
			notifyObservers(partyName);
		}
	}
	
	public List<String> getParties() {
		List<String> toReturn = new ArrayList<String>(parties.size());
		toReturn.addAll(parties);
		return toReturn;
	}
	
	public boolean hasParty(String partyName) {
		return parties.contains(partyName);
	}

}
