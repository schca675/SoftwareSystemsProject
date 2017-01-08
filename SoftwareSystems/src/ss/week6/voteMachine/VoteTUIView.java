package ss.week6.voteMachine;

import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Scanner;

public class VoteTUIView implements VoteView {
	private VoteMachine controller;
	
	public VoteTUIView(VoteMachine controller) {
		this.controller = controller;
	}

	public void start() {
		Scanner scanny = new Scanner(System.in);
		System.out.println("Please enter your input.");
		help();
		boolean stop = false;
		while (!stop) {
			if (scanny.hasNext()) {
				String input = scanny.next();
				switch (input) {
					case "VOTE":
						if (scanny.hasNext()) {
							controller.vote(scanny.next());
						}
						break;
					case "ADD":
						if (scanny.hasNext() && scanny.next().equals("PARTY") && scanny.hasNext()) {
							controller.addParty(scanny.next());
						}
						break;
					case "PARTIES":
						showParties(controller.getParties());
						break;
					case "VOTES":
						showVotes(controller.getVotes());
						break;
					case "EXIT":
						stop = true;
						break;
					case "HELP":
						help();
						break;
					default:
						help();
						break;
				}
			}
		}
		scanny.close();
	}
	
	public void showVotes(Map<String, Integer> votes) {
		for (String party: votes.keySet()) {
			System.out.println(party + " has " + votes.get(party) + " votes");
		}
	}
	
	public void showParties(List<String> parties) {
		for (String party : parties) {
			System.out.println(party);
		}
	}
	
	public void showError(String message) {
		System.out.println(message);
	}
	
	public void update(Observable observable, Object change) {
		if (observable instanceof PartyList) {
			System.out.println("Party " + (String) change + " has been registered");
		} else if (observable instanceof VoteList) {
			System.out.println("A vote has been cast for " + (String) change);
		}
	}
	
	private void help() {
		System.out.println("Available commands: VOTE [party], ADD PARTY [party], PARTIES, VOTES, "
				+ "EXIT, HELP");
	}
}
