package ss.week1;

public class ThreeWayLamp {

	private int currentSetting;
	
	public ThreeWayLamp() {
		currentSetting = 0;
	}
	
	public int getSetting() {
		return currentSetting;
	}
	
	public void switchSetting() {
		currentSetting = (currentSetting + 1) % 4;
	}

}
