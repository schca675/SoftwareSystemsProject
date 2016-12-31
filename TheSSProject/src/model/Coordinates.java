package model;

public class Coordinates {
	
	// <------ Instance variables ------>	
	private int x;
	private int y;
	
	// <------ Constructor ------>
	
	/**
	 * Creates new coordinates.
	 * @param x coordinate of the x axis
	 * @param y coordinate of the y axis
	 */
	//@ ensures getX() == x && getY() == y; 
	public Coordinates(int x, int y) {
		this.x = x;
		this.y = y;
	}

	/**
	 * Returns the x coordinate.
	 * @return the x coordinate.
	 */
	/*@ pure */ public int getX() {
		return this.x;
	}
	
	/**
	 * Returns the y coordinate.
	 * @return the y coordinate.
	 */
	/*@ pure */ public int getY() {
		return this.y;
	}
}
