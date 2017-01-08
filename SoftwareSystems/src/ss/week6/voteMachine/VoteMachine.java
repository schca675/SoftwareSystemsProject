package ss.week6.voteMachine;

import java.util.List;
import java.util.Map;

import ss.week6.voteMachine.gui.VoteGUIView;

public class VoteMachine {
	private PartyList partyList;
	private VoteList voteList;
	
	public VoteMachine() {
		partyList = new PartyList();
		voteList = new VoteList();
	}
	
	public void start() {
		VoteView view = new VoteGUIView(this);
		partyList.addObserver(view);
		voteList.addObserver(view);
		view.start();
	}
	
	public List<String> getParties() {
		return partyList.getParties();
	}
	
	public Map<String, Integer> getVotes() {
		return voteList.getVotes();
	}
	
	public void addParty(String party) {
		partyList.addParty(party);
	}
	
	public void vote(String party) {
		if (partyList.hasParty(party)) {
			voteList.addVote(party);
		}
	}

	public static void main(String[] args) {
		VoteMachine voteMachine = new VoteMachine();
		voteMachine.start();
	}
}
