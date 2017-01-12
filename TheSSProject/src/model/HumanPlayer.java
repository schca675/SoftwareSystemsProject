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
	//@ ensures this.name == name && this.playerID == id;
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
    public Coordinates determineMove(Board board) {
		String message = "It is your turn, " + this.name + " ("  
				+ this.playerID.toString() + "), what is your choice?";
		Coordinates coord = readCoord(message); 
		while (!board.checkMove(coord.getX(), coord.getY())) {
			coord = readCoord("Invalid choice: " + message);
		}
		return coord;
	}
	/**
	 * Reads the coordinates from System.in.
	 * 
	 * @param message Message that should be printed.
	 * @return Coordinates that the player entered.
	 */
	public Coordinates readCoord(String message) {
		int x = -1;
		int y = -1;
		int countInt = 0;
		Scanner line = new Scanner(System.in);
		// read until getting two integers.
		while (countInt < 2) {
			System.out.println(message);
			System.out.println("Write the coordinates in this form: x y");
			if (line.hasNextLine()) {
				Scanner scanny = new Scanner(line.nextLine());
				while (countInt < 2 && scanny.hasNextInt()) {
					if (countInt == 0) {
						x = scanny.nextInt();
					} else if (countInt == 1) {
						y = scanny.nextInt();
					}
					countInt = countInt + 1;
				}
				scanny.close();
				if (countInt != 2) {
					countInt = 0;
				}
			}		
		}
		return new Coordinates(x, y);
	}

}
