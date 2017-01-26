package exc;

public class TowerCoordinates {
	
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
	public TowerCoordinates(int x, int y) {
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
	
	/**
	 * Transforms the TowerCoordinates into a String.
	 * @return String representation of the TowerCoordinates.
	 */
	@Override
	public String toString() {
		return "x = " + x + ", y = " + y;
	}
	
	/**
	 * Compares two different TowerCoordinates.
	 * @return true if they are the same, false if they are not.
	 */
	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof TowerCoordinates)) {
			return false;
		} else {
			return ((TowerCoordinates) obj).getX() == x && ((TowerCoordinates) obj).getY() == y;
		}
	}
}
