package test;

import java.io.ByteArrayInputStream;
import java.io.InputStream;

import client.ClientTUI;

public class ClientTUITest {
	private String commands1;

	// HOW TO SETUP THIS TEST
	// 1. Launch ServerGUI on port 2727.
	// 2. Run a ClientTUI. Enter localhost for the IP, 2727 for the port and -N TestOpponent as name.
	// 3. Run this test.
	// 4. Compare the output of the console to this: http://pastebin.com/0KDitV3h
	public ClientTUITest() {
		this.commands1 = "";
		// Try to enter a wrong IP.
		addCommand("localsdfnjk");
		addCommand("234.234.11111.324");
		// Try to enter a correct IP.
		addCommand("localhost");
		// Try to enter a wrong port.
		addCommand("234234");
		addCommand("sdnfjksdbfjk");
		// Try to enter a correct port.
		addCommand("2727");
		// Try to connect with a valid name.
		addCommand("ClientTUITest");
		// Try to send some wrong invites.
		addCommand("PING");
		// Sends a help command.
		addCommand("HELP");
		// Ask for the leaderboard.
		addCommand("LEADERBOARD");
		// If the in stream is empty, the Client will terminate,
		// so just send some pings to make sure we receive other messages.
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		addCommand("PING");
		// Try to send some correct.
		InputStream in1 = new ByteArrayInputStream(commands1.getBytes());
		System.setIn(in1);
		ClientTUI ct = new ClientTUI();
		ct.addConnectMessage("addConnectMessage()");
		ct.addInviteMessage("addInviteMessage()");
		ct.addMoveMessage("addMoveMessage()");
		ct.addChatMessage("TestChatter addChatMessage()");
		ct.addLobbyMessage("addLobbyMessage()");
		ct.addErrorMessage("addErrorMessage()");
		ct.addPingMessage("addPingMessage()");
		ct.addHelpMessage("addHelpMessage()");
		ct.setUpClient();
	}

	public static void main(String[] args) {
		new ClientTUITest();
	}

	public void addCommand(String command) {
		commands1 += command + "\n";
	}
}
