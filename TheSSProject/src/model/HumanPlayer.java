package model;

import java.util.Scanner;

public class HumanPlayer extends Player {

	// <------ Constructors ------>
	
	/** 
	 * Creates a new human player with given name and ID. 
	 * 
	 * @param name Name of the player
	 * @param id Player ID of the player
	 */
	//@ requires name != null;
	//@ requires id == PlayerID.X || id == PlayerID.O;
	//@ ensures this.getName() == name && this.getPlayerID() == id;
	public HumanPlayer(String name, PlayerID id) {
		super(name, id);
	}
	
	// <------ Queries ------>
	
	/**
	 * Determines the coordinates of the field for the next move.
	 * 
	 * @param board current board, the game is played on.
	 * @return index of the field for the next move.
	 */
	//@ requires board != null && !board.isFull();
	//@ ensures board.checkMove(\result.getX(),\result.getY());
	@Override
	public Coordinates determineMove(Board<PlayerID> board) {
		// TODO Auto-generated method stub
		String message = "It is your turn, " + this.getName() + " (" 
				+ this.getPlayerID().toString() + "), what is your choice?";
		Coordinates coord = readCoord(message); 
		return null;
	}
	
	public Coordinates readCoord(String message) {
		boolean successfullReading = false;	
		Scanner scanny = new Scanner(System.in);
		while (!successfullReading) {
			
			
		}
		return null;
	}

}
