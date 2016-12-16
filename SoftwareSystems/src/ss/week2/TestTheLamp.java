package ss.week2;

public class TestTheLamp {
	
	public static void main(String[] args) {
		ThreeWayLamp7 test = new ThreeWayLamp7();
		System.out.println("Initialized the lamp, with value:");
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println("After fourth increment, should return to zero:");
		System.out.println(test.getSetting());
		test.switchSetting();
	}
	
}
