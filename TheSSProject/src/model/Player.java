package model;


public class Player {
	
	// <------ Instance variables ------>	
	
	public final String name;
	public final int playerID;
	
	// <------ Constructor ------>
	
	/** 
	 * Creates a new player with given name and ID. 
	 * 
	 * @param name Name of the player
	 * @param id Player ID of the player
	 */
	//@ requires name != null;
	//@ requires id >=0;
	//@ ensures this.name == name && this.playerID == id;
	public Player(String name, int id) {
		this.name = name;
		this.playerID = id;
	}
}
