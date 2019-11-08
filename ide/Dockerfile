# ----------------------------------------------------------------------------------
# Build ide
FROM maven:3.6.1-jdk-11 as build

WORKDIR /usr/src/mymaven

COPY pom.xml .
COPY src ./src

RUN mvn clean install -Duser.home=/var/maven -Dmaven.test.skip=true

# ----------------------------------------------------------------------------------
# Run ide

FROM tomcat:9.0.14-jre11 as app

COPY --from=build /usr/src/mymaven/target/decompositiondiversity.war /usr/local/tomcat/webapps/decompositiondiversity.war
COPY --from=build /usr/src/mymaven/target/decompositiondiversity     /usr/local/tomcat/webapps/decompositiondiversity

